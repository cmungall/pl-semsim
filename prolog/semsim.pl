/* -*- Mode: Prolog -*- */

:- module(semsim,
          [
           semsim_all_by_all/1,
           semsim_all_by_all/0,
           generate_term_indexes/0,
           semsim_compare_pair/4,
	   semsim_attribute_element_count/2,
	   semsim_attribute_IC/2,
           semsim_element_attributeset/2,
           semsim_element_exists/1,
           semsim_attribute_exists/1,
           semsim_element_pair/2,           
           semsim_pair_ci/3,
           semsim_pair_cu/3,
	   semsim_pair_subset_of/3,
           semsim_pair_simJ/3,
	   semsim_pair_simJ/5,
           semsim_pair_simJ_of_f1/3,
           semsim_pair_simJ_of_f2/3,
           semsim_pair_simGIC/3,
	   semsim_pair_simICratio/3,
           semsim_pair_maxIC/3,
           semsim_pair_maxIC_attributes/4,
           semsim_pair_cossim/3,
           semsim_pair_symmetric_bma_maxIC/3,
           semsim_pair_symmetric_bma_maxIC/4,
           semsim_pair_nr_ICatt_pairs/4,
           semsim_pair_nr_independent_atts/4,
           semsim_pair_nr_independent_atts_corrected/6,
           semsim_attributeset_pair_csumIC_atts/6,
           semsim_attributeset_pair_csumIC_atts/3,
           semsim_pair_pval_hyper/3,
           semsim_pair_pval_hyper/7,
           semsim_attribute_pair_pval_hyper/7,
           semsim_pair_all_scores/3,
           semsim_element_vector/2,
           semsim_element_matches/2,
           semsim_element_matches/3,
	   %vector_attributes/2,
	   %semsim_av_subsumes_element/2,
           rksort_with_limit/3
          ]).

/** <module> semantic similarity

  Predicates for comparing attributes based on their semantic
  similarity.

  This should be used in combination with a plugin module. For
  example, basic_rdfs provides inference using OWL classes and
  individuals.

  Note that this module depends on SWI-Prolog compiled with GMP
  support
  
*/


:- dynamic element_ix/2.
:- dynamic attribute_ix/2.
:- dynamic semsim_element_vector_cached/2.
:- dynamic attribute_vector_cached/2.
:- dynamic semsim_element_attribute/2.
:- dynamic semsim_element_attribute_direct/2.
:- dynamic semsim_element_attributeset_cached/2.
:- dynamic semsim_pair_score_cached/3.
:- dynamic attribute_subsumer_vector_cached/2. % new

:- multifile element_attribute_direct_hook/2.
:- multifile element_attribute_indirect_hook/2.
:- multifile semsim:attribute_ancestor_hook/2.

% ----------------------------------------
% Indexing
% ----------------------------------------


%% generate_term_indexes
%
% creates an initial index of all semsim_elements and attributes,
% using rdfs_individual_of/2 to specify the semsim_element to attribute relation.
%
% mappings stored in element_ix/2 and attribute_ix/2.
% these indexes do not need to be used directly by the library user,
% but they are used internally to map atoms to integer indexes
% for efficient lookup of attribute vectors
generate_term_indexes :-
        retractall(semsim:semsim_element_attribute_direct/2),
        forall(element_attribute_direct_hook(I,C),assert(semsim:semsim_element_attribute_direct(I,C))),
        retractall(semsim:semsim_element_attribute/2),
        setof(I,C^element_attribute_direct_hook(I,C),Is),
        forall((member(I,Is),element_attribute_indirect_hook(I,C)),assert(semsim:semsim_element_attribute(I,C))),
        retractall(semsim:semsim_element_vector_cached/2),
	debug(sim,'generating semsim_element ix',[]),
        generate_term_index(element_ix,Is),
	debug(sim,'generating attribute ix',[]),
        setof(C,I^semsim_element_attribute(I,C),Cs),
        generate_term_index(attribute_ix,Cs).

% generate_term_index(+Pred, +Terms:list) - private
%
% for each Term in Terms, generate a unit clause (fact):
%
%     Pred(Term,Num)
% 
% Such that the first term has Num=0 and the last has
% Num=count(Terms)-1
%
% Term can be any term, but in this module, this
% goal is only called with atoms, and with
% Base = element_id | attribute_ix
generate_term_index(Base, Terms) :-
        Clause =.. [Base,_,_],
        retractall(Clause),
        % this is a slightly ugly implementation,
        % but it avoids hitting the goal stack limit on
        % 32 bit machines
        nb_setval(n,0),
        forall(member(Term,Terms),
               (   nb_getval(n,Num),
                   Fact =.. [Base,Term,Num],
                   assert(Fact),
                   Num2 is Num+1,
                   nb_setval(n,Num2))),
        nb_getval(n,Max),
        debug(sim,'generated ~w ix; num=~w',[Base,Max]),
        index_countvar(Base,CountVar),
        nb_setval(CountVar,Max).

index_countvar(element_ix,semsim_element_count).
index_countvar(attribute_ix,attribute_count).

% ----------------------------------------
% Basic stats
% ----------------------------------------

%% semsim_element_count(?NumSemsim_elements:int)
semsim_element_count(X) :- nb_getval(semsim_element_count,X).

% nondet
semsim_element_exists(X) :- element_ix(X,_).
semsim_attribute_exists(X) :- attribute_ix(X,_).

%% semsim_element_pair(?I,?J) is nondet
semsim_element_pair(X,Y) :- element_ix(X,_),element_ix(Y,_).


%% attribute_count(?NumAttributes:int)
attribute_count(X) :- nb_getval(attribute_count,X).

%% semsim_attribute_element_count(?A,?NumSemsim_elements:int)
%
% number of semsim_elements that have attribute A
semsim_attribute_element_count(A,Num) :-
        attribute_ix(A,_),
        aggregate(count,I,element_attribute_indirect_hook(I,A),Num).

%% semsim_attribute_IC(?A,?IC:float)
% -log2(p(A))
% note: you may wish to memoize this using
% the blipkit tabling module
semsim_attribute_IC(A,IC) :-
        semsim_attribute_element_count(A,NumFA),
        semsim_element_count(NumF),
        IC is -(log(NumFA/NumF)/log(2)).

% ----------------------------------------
% Wrapper methods
% ----------------------------------------

semsim_all_by_all(SPairs) :-
        findall(Num-pair(F1,F2),
                (   element_ix(F1,Ix1),
                    element_ix(F2,Ix2),
                    Ix1<Ix2,
                    semsim_compare_pair(F1,F2,Num)),
                SPairs).

semsim_all_by_all :-
        retractall(semsim_pair_score_cached/3),
        element_ix(F1,Ix1),
        element_ix(F2,Ix2),
        Ix1<Ix2,
        semsim_compare_pair(F1,F2,Num),
        assert(semsim_pair_score_cached(F1,F2,Num)),
        fail.
semsim_all_by_all :- true.


%% semsim_element_matches(?F:atom,?Matches:list)
% what does F match?
semsim_element_matches(F,Matches) :-
        semsim_element_matches(F,Matches,[]).

%% semsim_element_matches(?F:atom,?Matches:list,+Opts:list)
% what does F match?
% Opts :
%   limit(Limit) - return top Limit hits
semsim_element_matches(F,Matches,Opts) :-
        member(min_ov(MinOv),Opts),
        !,
        findall(Num-F2,
                (   semsim_compare_pair(F,F2,Num,Opts),
                    Num>MinOv),
                Matches1),
        best_matches(Matches1,Matches,Opts).

semsim_element_matches(F,Matches,Opts) :-
        findall(Num-F2,
                semsim_compare_pair(F,F2,Num,Opts),
                Matches1),
        best_matches(Matches1,Matches,Opts).

best_matches(Matches,BestMatches,Opts) :-
        member(limit(Limit),Opts),
        !,
        rksort_with_limit(Matches,BestMatches,Limit).
best_matches(L,L2,_) :-
        keysort(L,SL),
        reverse(SL,L2).


semsim_av_subsumes_element(AV,F) :-
	semsim_element_vector(F,FV),
	VI is FV /\ AV,
	VI = AV.


% ----------------------------------------
% Similarity Metrics
% ----------------------------------------

%% semsim_pair_ci(?F1,?F2,?Num:int)
% intersection of attribute values:
% | attrs(F1) ∩ attrs(F2) |
%
% equivalent to the dot product between
% the two attribute vectors
semsim_pair_ci(F1,F2,Num) :-
        semsim_element_vector(F1,AV1),
        semsim_element_vector(F2,AV2),
        Num is popcount(AV1 /\ AV2).

%% semsim_pair_cu(?F1,?F2,?Num:int)
% union of attribute values:
% | attrs(F1) ∪ attrs(F2) |
semsim_pair_cu(F1,F2,Num) :-
        semsim_element_vector(F1,AV1),
        semsim_element_vector(F2,AV2),
        AVP = AV1 \/ AV2,
        Num is popcount(AVP).

%% semsim_pair_subset_of(?F1,?F2,S:number)
% degree to which F1 is a subset of F2.
% 1.0 iff every attribute of F1 is an attribute of F2
% 0.0 iff no attributes of F1 are attributes of F2
semsim_pair_subset_of(F1,F2,S) :-
        semsim_element_vector(F1,AV1),
        semsim_element_vector(F2,AV2),
        Num1 is popcount(AV1),
        NumBoth is popcount(AV1 /\ AV2),
	S is NumBoth/Num1.


%% semsim_pair_simJ(?F1,?F2,-Sim:float)
%
% Jacard similarity coefficient between two semsim_elements,
% based on their attribute vectors:
% | A1 ∩ A2| / | A1 ∪ A2|
% where A1 and A2 are the sets of positive attributes
% in F1 and F2 respectively
%
% Speed: the underlying implementation uses bitwise
% operations on ints, so it should be super-fast
semsim_pair_simJ(F1,F2,Sim) :-
        semsim_pair_cu(F1,F2,CU),
	CU > 0,
        semsim_pair_ci(F1,F2,CI),
        Sim is CI/CU.

%% semsim_pair_simJ(?F1,?F2,-Sim:float,NumInBoth:int,NumInEither:int)
semsim_pair_simJ(F1,F2,Sim,CI,CU) :-
        semsim_pair_cu(F1,F2,CU),
	CU > 0,
        semsim_pair_ci(F1,F2,CI),
        Sim is CI/CU.

%% semsim_pair_asymmetric_simJ(?F1,?F2,-Sim:float)
%
% | A1 | / | A1 ∪ A2|
semsim_pair_asymmetric_simJ(F1,F2,Sim) :-
        semsim_element_vector(F1,AV),
        CU is popcount(AV),
	CU > 0,
        semsim_pair_cu(F1,F2,CI),
        Sim is CI/CU.

semsim_pair_simJ_of_f1(F1,F2,Sim) :-
        semsim_element_vector(F1,AV),
        CU is popcount(AV),
	CU > 0,
        semsim_pair_ci(F1,F2,CI),
        Sim is CI/CU.

semsim_pair_simJ_of_f2(F1,F2,Sim) :-
        semsim_element_vector(F2,AV),
        CU is popcount(AV),
	CU > 0,
        semsim_pair_ci(F1,F2,CI),
        Sim is CI/CU.


%% semsim_pair_simGIC(?F1,?F2,-Sim:float)
% ∑ [a ∈ A1 ∩ A2] IC(a)  / ∑ [a ∈  A1 ∪ A2]IC(t)
% Ref:
% Pesquita, C.;Faria, D.;Bastos, H.;Falcão, AO.; Couto, FM. 
% Evaluating GO-based semantic similarity measures. Proceedings of the 10th Annual Bio-Ontologies Meeting (Bio-Ontologies 2007).
%
% Speed: bitvectors must be translated into lists
% so this is much slower than simJ
semsim_pair_simGIC(F1,F2,Sim) :-
        semsim_element_vector(F1,AV1),
        semsim_element_vector(F2,AV2),
        AVI is AV1 /\ AV2,
        AVU is AV1 \/ AV2,
        % note that here we have to translate the bit vector back to
        % a list of attributes. maybe bitvectors don't but us much for
        % this metric? use prolog sets instead?
        vector_sumIC(AVI,ICI),
        vector_sumIC(AVU,ICU),
        Sim is ICI/ICU.

semsim_pair_simICratio(F1,F2,Sim) :-
        semsim_element_vector(F1,AV1),
        semsim_element_vector(F2,AV2),
        AVI is AV1 /\ AV2,
        AVU is AV1 \/ AV2,
        % note that here we have to translate the bit vector back to
        % a list of attributes. maybe bitvectors don't but us much for
        % this metric? use prolog sets instead?
        vector_sumIC(AVI,ICI),
        Sim is ICI / popcount(AVU).


%% semsim_pair_simNRGIC(?F1,?F2,-Sim:float)
% ∑ [a ∈ nr(A1 ∩ A2)] IC(a)  / ∑ [a ∈  nr(A1) ∪ nr(A2)∪ nr(A1 ∩ A2)]IC(t)
%
% as semsim_pair_simGIC/3, taking the nonredundant nodes in the intersection set and each of the unique sets
% TODO
semsim_pair_simNRGIC(F1,F2,Sim) :-
        semsim_element_vector(F1,AV1),
        semsim_element_vector(F2,AV2),
        vector_nr(AV1,AV1NR),   % TODO
        vector_nr(AV2,AV2NR),
        AVI is AV1 /\ AV2,
        vector_nr(AVI,AVINR),
        AVU is AV1NR \/ AV2NR \/ AVI,
        vector_sumIC(AVINR,ICI),
        vector_sumIC(AVU,ICU),
        Sim is ICI/ICU.

%% semsim_pair_maxIC(?F1,?F2,-Max:float)
% Max[IC(a)] : a ∈ A1 ∩ A2
semsim_pair_maxIC(F1,F2,MaxIC) :-
        semsim_element_attributeset(F1,AL1),
        semsim_element_attributeset(F2,AL2),
        ord_intersection(AL1,AL2,AL_Both),
        maplist(semsim_attribute_IC,AL_Both,ICs),
        max_list(ICs,MaxIC).

/*
old___semsim_pair_maxIC(F1,F2,MaxIC) :-
        semsim_element_vector(F1,AV1),
        semsim_element_vector(F2,AV2),
        AVI is AV1 /\ AV2,
        % note that here we have to translate the bit vector back to
        % a list of attributes. maybe bitvectors don't buy us much for
        % this metric? use prolog sets instead?
        vector_maxIC(AVI,MaxIC).
*/

%% semsim_pair_maxIC_attributes(?F1,?F2,-Max:float,-Attributes:List)
% Max[IC(a)] : a ∈ A1 ∩ A2
semsim_pair_maxIC_attributes(F1,F2,MaxIC,MaxAL) :-
        semsim_element_attributeset(F1,AL1),
        semsim_element_attributeset(F2,AL2),
        ord_intersection(AL1,AL2,AL_Both),
        maplist(semsim_attribute_IC,AL_Both,ICs),
        max_list(ICs,MaxIC),
        list_pair_matches(AL_Both,ICs,MaxIC,MaxAL).

/*
old___semsim_pair_maxIC_attributes(F1,F2,MaxIC,AL) :-
        semsim_element_vector(F1,AV1),
        semsim_element_vector(F2,AV2),
        AVI is AV1 /\ AV2,
        vector_maxIC_attributes(AVI,MaxIC,AL).
*/

%% semsim_pair_maxIC_nr_attributes(+F1,+F2,?MaxIC,?AL_nr:list)
semsim_pair_maxIC_nr_attributes(F1,F2,MaxIC,AL_nr) :-
        semsim_pair_maxIC_attributes(F1,F2,MaxIC,AL),
        nr_subset(AL,AL_nr).

%% semsim_pair_nr_ICatt_pairs(+F1,+F2,SumIC:float,?Pairs:list)
semsim_pair_nr_ICatt_pairs(F1,F2,SumIC,SortedPairs) :-
        semsim_element_attributeset(F1,AL1),
        semsim_element_attributeset(F2,AL2),
        ord_intersection(AL1,AL2,AL_Both),
        nr_subset(AL_Both,AL_nr),
        setof(IC-A,
              (   member(A,AL_nr),
                  semsim_attribute_IC(A,IC)),
              Pairs),
        reverse(Pairs,SortedPairs),
        findall(IC,member(IC-_,Pairs),ICs),
        sumlist(ICs,SumIC).

%% semsim_pair_sumIC_ind_attributes(F1,F2,SumIC,SortedPairs)
% 
% calculate the sum of the ICs of the independent set of
% attributes shared by F1 and F2. The SumIC can be translated
% to a p-value.
%
% the set of independent attributes in common may include
% conjunctions of more than one attribute: e.g.
%
% [forelimb,hindlimb],[kidney],...
%
% here we treat forelimb and hindlimb as a conjunction, e.g.
% the phenotype co-manifests.
semsim_pair_nr_independent_atts(F1,F2,SumIC,SortedPairs) :-
        semsim_element_attributeset(F1,AL1),
        semsim_element_attributeset(F2,AL2),
        ord_intersection(AL1,AL2,AL_Both),
        nr_subset(AL_Both,AL_nr),
        debug(sim,'  NR ~w',[AL_nr]),
        combine_correlated_attributes(AL_nr,AL_independent),
        debug(sim,'  NR_Indep: ~w',[AL_independent]),
        setof(IC-A,
              (   member(A,AL_independent),
                  attributeset_information_content(A,IC)),
              Pairs),
        reverse(Pairs,SortedPairs),
        findall(IC,member(IC-_,Pairs),ICs),
        sumlist(ICs,SumIC).

semsim_pair_nr_independent_atts_corrected(F1,F2,N1,N2,SumIC,SortedPairs) :-
        semsim_element_attributeset(F1,AL1),
        semsim_element_attributeset(F2,AL2),
        semsim_semsim_attributeset_pair_csumIC_atts(AL1,AL2,N1,N2,SumIC,SortedPairs).

semsim_attributeset_pair_csumIC_atts(AL1,AL2,SumIC) :-
        semsim_attributeset_pair_csumIC_atts(AL1,AL2,_,_,SumIC,_).
semsim_attributeset_pair_csumIC_atts(AL1,AL2,N1,N2,SumIC,SortedPairs) :-
        ord_intersection(AL1,AL2,AL_Both),
        AL_Both\=[],
        length(AL1,N1),
        length(AL2,N2),
        debug(sim,'  size: ~w',[N1*N2]),
        nr_subset(AL_Both,AL_nr),
        debug(sim,'  NR ~w',[AL_nr]),
        combine_correlated_attributes(AL_nr,AL_independent),
        debug(sim,'  NR_Indep: ~w',[AL_independent]),
        length(AL_independent,N3),
        CorrectionFactor is N3/(sqrt(N1) * sqrt(N2)),
        CorrectionOffset is -log(CorrectionFactor)/log(2),
        solutions(IC-A,
                  (   member(A,AL_independent),
                      attributeset_information_content(A,IC_Raw),
                      IC is IC_Raw - CorrectionOffset,
                                %debug(sim,'    A: ~w = ~w - ~w',[A,IC_Raw,CorrectionOffset]),
                      IC>0),
                  Pairs),
        reverse(Pairs,SortedPairs),
        findall(IC,member(IC-_,Pairs),ICs),
        sumlist(ICs,SumIC).

attributeset_information_content([A],IC) :-
        !,
        semsim_attribute_IC(A,IC).
attributeset_information_content(Atts,IC) :-
        attributeset_semsim_element_vector(Atts,FV),
        NumFA is popcount(FV),
        semsim_element_count(NumF),
        IC is -(log(NumFA/NumF)/log(2)).

attributeset_semsim_element_vector([A|Atts],V_Out) :-
        attribute_vector(A,FV),
        attributeset_semsim_element_vector(Atts,FV,V_Out).

attributeset_semsim_element_vector([],V,V).
attributeset_semsim_element_vector([A|Atts],V_In,V_Out) :-
        attribute_vector(A,FV),
        V_Next is FV /\ V_In,
        attributeset_semsim_element_vector(Atts,V_Next,V_Out).

        

% given a set of atts, a1, a2, ..., an
% make a list of conjunction sets (represented as lists),
% c1, .., cm where each
% set c is a set of correlated attributes [a1, ..], where
% each member of the list is correlated with one other
combine_correlated_attributes(Atts,ConjAtts) :-
        findall([A],member(A,Atts),ConjAttsSeed),
        iteratively_combine_correlated_attributes(ConjAttsSeed,ConjAtts).

iteratively_combine_correlated_attributes(Atts,AttsOut) :-
        debug(sim,'  combining ~w',[Atts]),
        % TODO: pick *best* pairing
        select(ASet1,Atts,Atts2),
        select(ASet2,Atts2,Atts3),
        combine_asets_if_correlated(ASet1,ASet2,ASet3),
        % new: make sure everything in group is correlated. greedy
        forall( (member(A1,ASet3), member(A2,ASet3), A1 @< A2),
                correlated_attribute_pair(A1,A2)),
        debug(sim,'   ~w + ~w ==> ~w',[ASet1,ASet2,ASet3]),
        !,
        iteratively_combine_correlated_attributes([ASet3|Atts3],AttsOut).
iteratively_combine_correlated_attributes(Atts,Atts) :- !.

combine_asets_if_correlated(Set1,Set2,SetJ) :-
        member(A1,Set1),
        member(A2,Set2),
        correlated_attribute_pair(A1,A2),
        append(Set1,Set2,SetJ).

% more split groups increases chance of groups being filtered when ICs for groups are corrected
correlated_attribute_pair(A1,A2) :-
        semsim_attribute_pair_pval_hyper(A1,A2,Vk,_Vn,_Vm,_VN,P),
        %debug(sim,'   ~w',[semsim_attribute_pair_pval_hyper(A1,A2,Vk,_Vn,_Vm,_VN,P)]),
        P < 0.000001, % HARCODE ALERT. TODO - use overlap as well
        Vk > 2.

/*
attribute_correction_factor(N) :-
        aggregate(count,A,attribute_used_at_least_twice(A),N).

attribute_used_at_least_twice(A) :-
        attribute_vector(A,V),
        N is popcount(V),
        N > 1.
*/
        
%% nr_subset(+AL_In:list,:AL_NR:lsit) is det
% true if AL_NR is the non-redundant subset of AL_In.
% requires attribute_subsumer/2
nr_subset(AL1,AL2) :-
        findall(A,
                (   member(A,AL1),
                    \+ ((member(A2,AL1),
                         A2\=A,
                         attribute_ancestor_hook(A2,A),
                         \+ attribute_ancestor_hook(A,A2)))),
                AL2).



%% semsim_pair_cossim(?F1,?F2,-Sim:float)
% cosine similarity between two semsim_element attributes
% vectors.
%
% ==
%           A1.A2
% acos  ------------
%       ||A1||.||A2||
% ==
% Since the angle, θ, is in the range of [0,π],
% the resulting similarity will yield the value of π as meaning exactly opposite,
% π / 2 meaning independent, 0 meaning exactly the same, with in-between values indicating intermediate similarities or dissimilarities.
semsim_pair_cossim(F1,F2,Sim) :-
        semsim_element_vector(F1,AV1),
        semsim_element_vector(F2,AV2),
        AVP = AV1 /\ AV2,
        DP is popcount(AVP), % dot product
        M1 is popcount(AV1),
        M2 is popcount(AV2),
        Sim is acos(DP / (sqrt(M1)*sqrt(M2))).

semsim_pair_symmetric_bma_maxICnr(F1,F2,Sim,AL_nr) :-
        semsim_pair_symmetric_bma_maxIC(F1,F2,Sim,AL),
        maplist(nr_subset,AL,AL_nr).

%% semsim_pair_symmetric_bma_maxIC(F1,F2,Sim)
semsim_pair_symmetric_bma_maxIC(F1,F2,Sim) :-
        semsim_pair_symmetric_bma_maxIC(F1,F2,Sim,_).

%% semsim_pair_symmetric_bma_maxIC(?F1,?F2,?BMA:float,?AttributeSets:list)
%
% for each direct attribute, find the best match(es) in the other set.
% do this symmetrically for both F1 and F2
%
semsim_pair_symmetric_bma_maxIC(F1,F2,Sim,AL) :-
        element_ix(F1,_),       % ensure ground
        element_ix(F2,_),       % ensure ground
        semsim_pair_compare_all_atts_maxIC(F1,F2,Set1vs2),
        semsim_pair_compare_all_atts_maxIC(F2,F1,Set2vs1),
        union(Set1vs2,Set2vs1,Set),
        findall(MaxIC,member(MaxIC-_,Set),MaxICs),
        sumlist(MaxICs,MaxICSum),
        length(MaxICs,Len),
        Sim is MaxICSum/Len,
        findall(A,member(_-A,Set),AL).

semsim_pair_compare_all_atts_maxIC(F1,F2,Set) :-
        setof(MaxIC-AMs,A^semsim_pair_attribute_maxIC_set(F1,F2,A,MaxIC,AMs),Set).


% semsim_pair_attribute_maxIC_set(?F1,?F2,?Att,-Max:float,?AttributesWithMax:list)
%
% for (+F1,+F2,+Att) this is deterministic.
% if Att is in A(F1) then find the best att A2(s) in A(F2) with its IC.
% there may be multiple such attributes, which is why we use a list
semsim_pair_attribute_maxIC_set(F1,F2,A,MaxIC,AM) :-
        % TODO - fix this to use sets  and ord_intersection
        semsim:semsim_element_attribute_direct(F1,A), % data unit-clause
        attribute_subsumer_vector(A,AV1), % derived from attribute_subsumer
        semsim_element_vector(F2,AV2),
        AVI is AV1 /\ AV2,
        vector_maxIC_attributes(AVI,MaxIC,AM).

% NOTE: this makes more sense comparing attributes
%  by their semsim_elements
semsim_pair_pval_hyper(F1,F2,P) :-
        semsim_pair_pval_hyper(F1,F2,_,_,_,_,P).
semsim_pair_pval_hyper(F1,F2,Vk,Vn,Vm,VN,P) :-
        semsim_element_vector(F1,AV1),
        semsim_element_vector(F2,AV2),
        AV_Common = AV1 /\ AV2,
        Vk is popcount(AV_Common),
        Vn is popcount(AV1),
        Vm is popcount(AV2),
        attribute_count(VN),
        p_value_by_hypergeometric(Vk,Vn,Vm,VN,P).

semsim_pair_all_scores(F1,F2,Scores) :-
        element_ix(F1,_),
        element_ix(F2,_),
        (   var(Scores)
        ->  default_scores(Scores)
        ;   true),        
        (   memberchk(simTO(SimTO),Scores)
        ->  semsim_pair_ci(F1,F2,SimTO)
        ;   true),
        (   memberchk(simJ(SimJ),Scores)
        ->  semsim_pair_simJ(F1,F2,SimJ)
        ;   true),
        (   memberchk(simGIC(SimGIC),Scores)
        ->  semsim_pair_simGIC(F1,F2,SimGIC)
        ;   true),
        (   memberchk(simNRGIC(SimNRGIC),Scores)
        ->  semsim_pair_simNRGIC(F1,F2,SimNRGIC)
        ;   true),
        (   memberchk(maxIC(MaxIC),Scores)
        ->  semsim_pair_maxIC(F1,F2,MaxIC)
        ;   true),
        (   memberchk(maxIC(MaxIC,MaxICAttrs),Scores)
        ->  semsim_pair_maxIC_attributes(F1,F2,MaxIC,MaxICAttrs)
        ;   true),
        (   memberchk(maxICnr(MaxIC,MaxICAttrs),Scores)
        ->  semsim_pair_maxIC_nr_attributes(F1,F2,MaxIC,MaxICAttrs)
        ;   true),
        (   memberchk(symmetric_bma_maxIC(ICCS,CSSL),Scores)
        ->  semsim_pair_symmetric_bma_maxIC(F1,F2,ICCS,CSSL)
        ;   true),
        (   memberchk(symmetric_bma_maxICnr(ICCS,CSSL),Scores)
        ->  semsim_pair_symmetric_bma_maxICnr(F1,F2,ICCS,CSSL)
        ;   true),
        !.

default_scores([simTO(_),
                simJ(_),
                simGIC(_),
                maxIC(_,_),
                symmetric_bma_maxIC(_,_)]).


%% semsim_compare_pair(+F1,+F2,-Score,+Opts)
% Opts :
%  metric(Metric) - one of simJ, cossim, ci, or a list of Metrics. defaults to simJ
semsim_compare_pair(F1,F2,Score,Opts) :-
        (   member(metric(Metric),Opts)
        ->  true
        ;   Metric=simJ),
        semsim_compare_pair_by_metric(F1,F2,Score,Metric,Opts).
semsim_compare_pair(F1,F2,Score) :-
        semsim_compare_pair(F1,F2,Score,[]).

% in the case where multiple metrics are required, the score is of
% the form MainScore-[score(M1,S1),score(M2,S2),...].
% thus the result can still be used in a keysort
semsim_compare_pair_by_metric(F1,F2,AllScore,L,Opts) :-
        L=[MainMetric|_],
        !,
        element_ix(F1,_),
        element_ix(F2,_),
        % this is inefficient as the same operations are performed
        % multiple times. TODO: optimize
        findall(score(Metric,Score),
                (   member(Metric,L),
                    semsim_compare_pair_by_metric(F1,F2,Score,Metric,Opts)),
                Scores),
        member(score(MainMetric,MainScore),Scores),
        AllScore=MainScore*Scores.

semsim_compare_pair_by_metric(F1,F2,MaxIC-MaxICAttrs,maxIC,_Opts) :-
        !,
        semsim_pair_maxIC_attributes(F1,F2,MaxIC,MaxICAttrs).
semsim_compare_pair_by_metric(F1,F2,Score,simJ,_Opts) :-
        !,
        semsim_pair_simJ(F1,F2,Score).
semsim_compare_pair_by_metric(F1,F2,Score,cossim,_Opts) :-
        !,
        semsim_pair_cossim(F1,F2,Score).
semsim_compare_pair_by_metric(F1,F2,Score,simGIC,_Opts) :-
        !,
        semsim_pair_simGIC(F1,F2,Score).
semsim_compare_pair_by_metric(F1,F2,Score,symmetric_bma_maxIC,_Opts) :-
        !,
        semsim_pair_symmetric_bma_maxIC(F1,F2,Score).
semsim_compare_pair_by_ci(F1,F2,Score,ci,_Opts) :-
        !,
        semsim_pair_ci(F1,F2,Score).

%% semsim_element_vector(?Semsim_element:atom,-AttributeVector:int)
% relationship between a Semsim_element and a vector of binary attribute values,
% encoded as a large int (the GMP library is required).
% The attribute vector has a bit set at position N (i.e. 2**N) if the semsim_element has attribute N
% (where the mapping between the attribute and N is in attribute_ix/2).
% 
% this is calculated for a semsim_element f as: ∑ [a ∈ fa(f)] 2**ix(a)
% (where ix is the index function and fa returns the set of attributes for a semsim_element)
semsim_element_vector(F,V) :-
        var(F),
        !,
        element_ix(F,_),        % ground F then calculate
        semsim_element_vector(F,V).
        
semsim_element_vector(F,V) :-
        nonvar(F),
        semsim_element_vector_cached(F,V),
        !.

semsim_element_vector(F,V) :-
        solutions(Num,(element_attribute_indirect_hook(F,Attribute),attribute_ix(Attribute,AI),Num is 2**AI),Nums),
        sumlist(Nums,V),
        assert(semsim_element_vector_cached(F,V)).

semsim_element_attributeset(F,AL) :-
        var(F),
        !,
        semsim_element_exists(F),
        semsim_element_attributeset(F,AL).
semsim_element_attributeset(F,AL) :-
        nonvar(F),
        semsim_element_attributeset_cached(F,AL),
        !.
semsim_element_attributeset(F,AL) :-
        setof(A,semsim_element_attribute(F,A),AL),
        assert(semsim_element_attributeset_cached(F,AL)).


%% attribute_vector(?Attribute:atom,-AttributeVector:int)
%
% relationship between a Attribute and a vector of binary attribute values,
% representing semsim_elements with this attribute,
% encoded as a large int (the GMP library is required).
%
% The attribute vector has a bit set at position N (i.e. 2**N) if the semsim_element N has the attribute
% (where the mapping between the semsim_element and N is in element_ix/2).
% 
% this is calculated for a attribute a as: ∑ [f ∈ af(a)] 2**ix(f)
% (where ix is the index function and af returns the set of semsim_elements for a attribute)
attribute_vector(A,V) :-
        var(A),
        !,
        attribute_ix(A,_),        % ground A then calculate
        attribute_vector(A,V).
        
attribute_vector(A,V) :-
        nonvar(A),
        attribute_vector_cached(A,V),
        !.

attribute_vector(A,V) :-        % A is ground, value is not yet cached
        template(Semsim_element,A,Goal), % get semsim_elements for this attribute
        % ∑ [f ∈ af(a)] 2**ix(f)
        solutions(Num,(Goal,element_ix(Semsim_element,AI),Num is 2**AI),Nums),
        sumlist(Nums,V),
        assert(attribute_vector_cached(A,V)).

%% semsim_attribute_pair_pval_hyper(+A1,+A2,?P:float)
%
% calculates correlation between two attributes based
% on shared semsim_elements
semsim_attribute_pair_pval_hyper(A1,A2,P) :-
        semsim_attribute_pair_pval_hyper(A1,A2,_,_,_,_,P).
semsim_attribute_pair_pval_hyper(A1,A2,Vk,Vn,Vm,VN,P) :-
        attribute_vector(A1,FV1),
        attribute_vector(A2,FV2),
        FV_Common = FV1 /\ FV2,
        Vk is popcount(FV_Common),
        Vn is popcount(FV1),
        Vm is popcount(FV2),
        attribute_count(VN),
        p_value_by_hypergeometric(Vk,Vn,Vm,VN,P).


% attribute_subsumer_vector(+Att,-AttSubsumerVector:int)
% maps an attribute to an integer bitvector for all subsuming (parent) attributes
attribute_subsumer_vector(A,ASV) :-
        solutions(P,attribute_ancestor_hook(A,P),Ps), % from data
        solutions(PI,(member(P,Ps),attribute_ix(P,PI)),PIs),
        solutions(Num,(member(PI,PIs),Num is 2**PI),Nums),
        sumlist(Nums,ASV),
        assert(attribute_subsumer_vector_cached(A,ASV)).

%% semsim_element_avcount(?F:atom,-Num:int)
% true if F has Num attributes set
semsim_element_avcount(F,Num) :-
        %semsim_element_vector(F,V),
        %Num is popcount(V).
        semsim_element_attributeset(F,AL),
        length(AL,Num).

% todo: use prolog sets?
vector_sumIC(AV,SumIC) :-
        vector_attributes(AV,AL),
        maplist(semsim_attribute_IC,AL,ICs),
        sumlist(ICs,SumIC).

% given a vector of attributes, find the max IC of all attributes
vector_maxIC(AV,MaxIC) :-
        vector_attributes(AV,AL),
        maplist(semsim_attribute_IC,AL,ICs),
        max_list(ICs,MaxIC).

% DEPRECATED
% vector_maxIC_attributes(+AV:int, ?MaxIC:float, ?MaxAL:list)
% as vector_maxIC/2, but include all attributes with IC matching MaxIC
vector_maxIC_attributes(AV,MaxIC,MaxAL) :-
        vector_attributes(AV,AL),
        maplist(semsim_attribute_IC,AL,ICs),
        max_list(ICs,MaxIC),
        list_pair_matches(AL,ICs,MaxIC,MaxAL).

list_pair_matches([],[],_,[]).
list_pair_matches([A|AL],[MaxIC|ICs],MaxIC,[A|MaxAL]) :-
        !,
        list_pair_matches(AL,ICs,MaxIC,MaxAL).
list_pair_matches([_|AL],[_|ICs],MaxIC,MaxAL) :-
        !,
        list_pair_matches(AL,ICs,MaxIC,MaxAL).

        

%% vector_attributes(+AV:int,?AL:list)
% True if AV is an integer bit vector with the attributes in AL set
vector_attributes(AV,AL) :-
        vector_attributes(AV,AL,16).

vector_attributes(AV,AL,Window) :-
        Mask is 2**Window -1,
        vector_attributes(AV,ALx,0,Window,Mask),
        flatten(ALx,AL).

%% vector_attributes(+AV:int,?AL:list,+Pos,+Window,+Mask) is det
% Mask must = Window^2 -1 (not checked)
% shifts AV down Window bits at a time. If there are any bits in the window,
% use vector_attributes_lo/2 to get the attribute list from this window.
% note resulting list must be flattened.
% todo: difference list impl?
vector_attributes(0,[],_,_,_) :- !.
vector_attributes(AV,AL,Pos,Window,Mask) :-
        !,
        NextBit is AV /\ Mask,
        AVShift is AV >> Window,
        NextPos is Pos+Window,
        (   NextBit=0
        ->  vector_attributes(AVShift,AL,NextPos,Window,Mask)
        ;   vector_attributes_lo(NextBit,ALNew,Pos),
            AL=[ALNew|AL2],
            vector_attributes(AVShift,AL2,NextPos,Window,Mask)).
        
% as vector_attributes/2, but checks one bit at a time
vector_attributes_lo(AV,AL) :-
        vector_attributes_lo(AV,AL,0).

vector_attributes_lo(0,[],_) :- !.
vector_attributes_lo(AV,AL,Pos) :-
        NextBit is AV /\ 1,
        AVShift is AV >> 1,
        NextPos is Pos+1,
        (   NextBit=1
        ->  attribute_ix(Att,Pos),
            AL=[Att|AL2]
        ;   AL=AL2),
        !,
        vector_attributes_lo(AVShift,AL2,NextPos).

% ----------------------------------------
% util
% ----------------------------------------

%% solutions(+Template,+Goal,-Set)
%   deterministic setof (will not fail). Goal is existentially quantified
solutions(X,Goal,Xs):-
        (   setof(X,Goal^Goal,Xs)
        ->  true
        ;   Xs=[]).

rksort_with_limit(L,L2,Limit) :-
        keysort(L,SL),
        reverse(SL,RSL),
        take_n(RSL,L2,Limit).

take_n([],[],_) :- !.
take_n(_,[],0) :- !.
take_n([H|L],[H|L2],N) :-
        Nm1 is N-1,
        take_n(L,L2,Nm1).


