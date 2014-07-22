/** <module> plugin to make semsim uses rdfs_individual_of

  Predicates for comparing RDF classes based on their semantic
  similarity, or RDF individuals, based on the similarity of the
  classes they instantiate.
  
*/

:- module(basic_rdfs,
          []).

:- use_module(library(semweb/rdf_db)).
:- use_module(library(semweb/rdfs)).
:- use_module(library(semsim)).

:- multifile semsim:element_attribute_direct_hook/2.
:- multifile semsim:element_attribute_indirect_hook/2.
:- multifile semsim:attribute_ancestor_hook/2.

semsim:element_attribute_direct_hook(I,C) :-
        rdf(I,rdf:type,C),
        rdf(C,rdf:type,owl:'Class').
semsim:element_attribute_indirect_hook(I,C) :-
        rdfs_individual_of(I,C),
        rdf(C,rdf:type,owl:'Class').
semsim:attribute_ancestor_hook(C,D) :-
        rdfs_subclass_of(C,D).



