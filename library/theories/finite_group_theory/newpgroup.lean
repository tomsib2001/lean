import data algebra.group .subgroup .finsubg theories.number_theory.pinat .cyclic

open nat finset fintype group_theory


definition pred_p [reducible] (p : nat) : nat → Prop := λ n, n = p

variables {G : Type} [ambientG : group G] [finG : fintype G] [deceqG : decidable_eq G]
include ambientG deceqG finG

section groups_missing

lemma subset_one_group (A : finset G) (hA : is_finsubg A) : subset '{(1:G)} A :=
begin
  rewrite subset_eq_to_set_subset,
  intro x,
  rewrite to_set_insert,
  rewrite to_set_empty,
  intro Hx,
  apply sorry
  end

lemma card1 : card ('{(1:G)}) = 1 :=
  calc
  card ('{(1:G)}) = card (empty) + 1 : card_insert_of_not_mem (!not_mem_empty)
  ...             = 0 + 1 : {card_empty}
  ...             = 1 : nat.add_zero

end groups_missing


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
:= finset.card (fin_lcosets B A)

definition Hall [reducible] (A B : finset G) :=
subset A B ∧ coprime (card A) (index A B)

definition pHall [reducible] (pi : ℕ → Prop) [Hdecpi : ∀ p, decidable (pi p)] (A B : finset G) :=
subset A B ∧ pgroup pi A ∧ is_pi'_nat pi (index A B)

-- the set of p-Sylows of a subset A
definition Syl (p : nat) (A : finset G) :=
{ S ∈ finset.powerset A | pHall (pred_p p) S A }


-- Definition Sylow A B := p_group B && Hall A B.
definition is_sylow p (A B : finset G) := pgroup (pred_p p) A ∧ Hall A B

-- subset_eq_to_set_subset

set_option formatter.hide_full_terms false

-- (hB : is_finsubg B)

lemma foo (B : finset G) : group_theory.fin_lcosets B '{(1:G)} = (finset.insert (group_theory.fin_lcoset B (1:G)) empty) := sorry

print image

lemma image_singleton {A B : Type} [hA: decidable_eq A] [hB: decidable_eq B] (f : A → B) (a : A) : image f (insert a empty) =  insert (f a) empty :=
begin
rewrite image_insert
end

-- lemma lcoset_one (B : finset G): (fin_lcosets B '{(1:G)}) = insert (fin_lcoset B 1) empty :=
-- let f := (λ x, fin_lcoset B x) in
--   image_singleton f

print image_singleton

lemma index_one (B : finset G)  : index '{(1:G)} B = card B :=
begin
  rewrite image_singleton
end

-- calc
--   index '{(1:G)} B = finset.card (fin_lcosets B ('{(1:G)} : finset G)) : rfl
--  ...               = finset.card (finset.insert (fin_lcoset B 1) finset.empty) : {image_singleton (fin_lcoset 1)}
--  ...               = finset.card B : {fin_lcoset_id}


lemma Hall1 (A : finset G) [h_A_gr : is_finsubg A] : Hall '{(1:G)} A :=
  and.intro (subset_one_group A h_A_gr)
  begin
    rewrite (index_one A),
    rewrite card1,
    exact (gcd_one_left (finset.card A))
  end

lemma p_group1 (p : nat) : pgroup (pred_p p) '{(1:G)} :=
and.intro
  begin
    rewrite card1,
    apply nat.le_refl
  end
  (take p Hp,
  absurd Hp (not_mem_empty p)
  )
-- lemma sylow1 p (B : finset G): is_sylow p '{(1:G)} B  := _
