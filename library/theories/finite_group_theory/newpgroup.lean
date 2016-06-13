import data algebra.group .subgroup .finsubg theories.number_theory.pinat .cyclic

open nat finset fintype group_theory

definition pred_p [reducible] (p : nat) : nat → Prop := λ n, n = p

variables {G : Type} [ambientG : group G] [finG : fintype G] [deceqG : decidable_eq G]
include ambientG deceqG finG

definition pgroup [reducible] (pi : ℕ → Prop) (H : finset G) := is_pi_nat pi (card H)

lemma pgroup_dec (pi : ℕ → Prop) [Hdecpi : ∀ p, decidable (pi p)] (H : finset G) :
decidable (pgroup pi H) := _

lemma test (H : finset G) : decidable (card H = 1)

lemma toto (pi : ℕ → Prop) [Hdecpi : ∀ p, decidable (pi p)] (H : finset G)
: decidable (pgroup pi H) := _


definition p_subgroup (pi : ℕ → Prop) (H1 H2 : finset G) := subset H1 H2 ∧ pgroup pi H1

definition p_elt (pi : ℕ → Prop) (x : G) : Prop := is_pi_nat pi (order x)

-- the index of the subgroup A inside the group B
definition index [reducible] (A B : finset G) -- (Psub : finset.subset A B)
:= finset.card (group_theory.fin_lcosets A B)

definition Hall [reducible] (A B : finset G) := 
subset A B ∧ coprime (card B) (index A B)

definition pHall [reducible] (pi : ℕ → Prop) [Hdecpi : ∀ p, decidable (pi p)] (A B : finset G) := 
subset A B ∧ pgroup pi A ∧ is_pi'_nat pi (index A B) 

-- the set of p-Sylows of A
definition Syl (p : nat) (A : finset G) := 
{ S ∈ finset.powerset A | pHall (pred_p p) S A }
