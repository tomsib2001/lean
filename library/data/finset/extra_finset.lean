import data.fintype.basic data.nat data.list.perm data.finset algebra.binary
open nat quot list subtype binary function eq.ops finset


section set_operations
lemma subset_inter {T : Type} [Hdeceq : decidable_eq T] {A B C : finset T} :
  A ⊆ B → A ⊆ C → A ⊆ B ∩ C := sorry

lemma finset_inter_subset_left {T : Type} [Hdeceq : decidable_eq T] {A B  : finset T} :
  A ∩ B ⊆ A := sorry

lemma finset_inter_subset_right {T : Type} [Hdeceq : decidable_eq T] {A B  : finset T} :
  A ∩ B ⊆ B := sorry

-- why is this hard to prove?
lemma missing_compl_compl {T : Type} [HfT : fintype T] [Hdeceq : decidable_eq T] (A : finset T) : finset.compl (finset.compl A) = A :=
  sorry

-- less sure that the next two are really necessary

lemma image_singleton {A B : Type} [hA: decidable_eq A] [hB: decidable_eq B] (f : A → B) (a : A) :
image f (insert a empty) =  insert (f a) empty :=
begin
rewrite image_insert
end

lemma insert_empty {A : Type} [hAdec : decidable_eq A] (a : A) (b : A) :
finset.insert a finset.empty = insert b empty → a = b :=
assume Heq_set,
have Hab : mem a (insert b empty), from (eq.subst Heq_set (mem_insert a empty)),
or.elim (eq.subst (mem_insert_eq a b empty) Hab) (take H, H)
begin
intro Habs,
exact false.elim (not_mem_empty a Habs)
end


end set_operations

section finset_of_fintype


definition fintype_of_finset [instance] {T : Type} [HfT : fintype T] : fintype (finset T) := sorry

end finset_of_fintype

section minmax

variables [T : Type] [HfT : fintype T] [Hdeceq : decidable_eq T]

include Hdeceq HfT

definition minSet [reducible] (P : finset T → Prop) (A : finset T) :=
  ∀ (B : finset T), B ⊆ A → (P B ↔ B = A)

definition decidable_minset [instance] (P : finset T → Prop) [HdecP : ∀ B, decidable (P B)] (A : finset T) : decidable (minSet P A) := _

lemma minsetp (P : finset T → Prop) (A : finset T) (HminSet : minSet P A) : P A :=
  iff.elim_right (HminSet A (subset.refl A)) (!rfl)

lemma minsetinf (P : finset T → Prop) (A B : finset T) (HminSet : minSet P A) (HPB : P B)
(Hsubset : subset B A) : B = A :=
  iff.elim_left (HminSet B Hsubset) HPB

lemma in_empty_empty (A : finset T) : subset A ∅ → A = ∅ :=
 λ H, iff.elim_left (subset_empty_iff A) H

lemma minSet_empty (P : finset T → Prop) (Hempty : P ∅) : minSet P ∅ :=
  take B HBinEmpty,
  have HBempty : B = ∅, from in_empty_empty B HBinEmpty,
  iff.intro
  (assume HPB, HBempty) (assume Heq : B = ∅, eq.substr Heq Hempty)

lemma helper_lemma (P : finset T → Prop) : (exists U, subset U ∅ ∧ P U) → exists U, minSet P U ∧ subset U ∅ :=
  assume (H : (exists U, subset U ∅ ∧ P U)),
  obtain (U : finset T) (HU : subset U ∅ ∧ P U), from H,
  have Hempty : U = ∅, from iff.elim_left (subset_empty_iff U) (and.left HU),
  have HPU : P U, from (and.right HU),
  exists.intro U (and.intro (eq.substr Hempty (minSet_empty P (eq.subst Hempty HPU))) (and.left HU))


definition smallest (P : nat → Prop) [HdecP : forall A, decidable (P A)]
(n : nat)  : P n → exists m, m ≤ n ∧ P m ∧ ∀ k, k ≤ n → k < m → ¬ P k :=
  have Hgeneral : ∀ p, p ≤ n → P p → exists m, m ≤ p ∧ P m ∧ ∀ k, k ≤ n → k < m → ¬ P k, from sorry,
  Hgeneral n (nat.le_refl n)

lemma minSet_exists (P : finset T → Prop) [HdecP : forall A, decidable (P A)](C : finset T) (HPC : P C) :
  exists A, minSet P A ∧ subset A C :=
  sorry

definition maxSet (P : finset T → Prop) (A : finset T) :=
  minSet (λ B, P (compl B)) (compl A)

definition decidable_maxset [instance] (P : finset T → Prop) [HdecP : ∀ B, decidable (P B)] (A : finset T) : decidable (maxSet P A) := decidable_minset _ _

lemma maxsetp {P : finset T → Prop} {A : finset T} : maxSet P A → P A :=
 assume H : minSet (λ B, P (finset.compl B)) (finset.compl A),
 have H1 : (λ B, P (-B)) (-A), from minsetp (λ B, P (finset.compl B)) (finset.compl A) H,
 eq.subst (missing_compl_compl A) H1

-- can't find the two lemmas which would make this easy
lemma maxsetsup (P : finset T → Prop) (A B : finset T) : maxSet P A → P B → A ⊆ B → B = A :=
  assume (Hmax : maxSet P A) HPB HsAB,
  have H : _, from minsetinf (λ B, P (compl B)) (compl A) (compl B) Hmax (eq.substr (missing_compl_compl B) HPB) sorry,
  sorry

lemma maxSet_exists (P : finset T → Prop) [HdecP : forall A, decidable (P A)](C : finset T) (HPC : P C) :
  exists A, maxSet P A ∧ subset C A :=
  have H : _,  from minSet_exists (λ B, P (compl B)) (compl C) (eq.substr (missing_compl_compl C) HPC),
  obtain A HA, from H,
  exists.intro (compl A)
  (and.intro
  (eq.substr (missing_compl_compl A) (and.left HA))
  sorry)

lemma maxSet_iff {P : finset T → Prop} {A : finset T} : maxSet P A ↔ (∀ B, A ⊆ B → (P B ↔ B = A)) :=
  iff.intro
  (assume HmaxSet,
  sorry)
  (assume Hdef,
   sorry)

end minmax

