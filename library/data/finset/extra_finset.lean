import data.fintype.basic data.nat data.list.perm data.finset algebra.binary algebra.ordered_ring
open nat quot subtype binary function eq.ops finset

section set_operations

lemma subset_inter {T : Type} [Hdeceq : decidable_eq T] {A B C : finset T}
(sAB :A ⊆ B) (sAC : A ⊆ C) : A ⊆ B ∩ C :=
  begin
  apply subset_of_forall,
  intro x HxA,
  apply mem_inter,
  apply (mem_of_subset_of_mem sAB),
  exact HxA,
  apply (mem_of_subset_of_mem sAC),
  exact HxA,
  end

lemma finset_inter_subset_left {T : Type} [Hdeceq : decidable_eq T] {A B  : finset T} :
  A ∩ B ⊆ A :=
  begin
  apply subset_of_forall,
  intros x HxAintB,
  apply (finset.mem_of_mem_inter_left HxAintB),
  end

lemma finset_inter_subset_right {T : Type} [Hdeceq : decidable_eq T] {A B  : finset T} :
  A ∩ B ⊆ B :=
  begin
    apply subset_of_forall,
    intros x HxAintB,
    apply (finset.mem_of_mem_inter_right HxAintB),
  end

lemma subset_compl {T : Type} [HfT : fintype T] [Hdeceq : decidable_eq T] {A B : finset T} (sAB : A ⊆ B) : finset.compl B ⊆ finset.compl A :=
  subset_of_forall (take x HxB,
  begin
   apply mem_compl,
   have HnB: x ∉ B, from (not_mem_of_mem_compl HxB),
   intro HxA,
   apply HnB,
   apply mem_of_subset_of_mem sAB HxA,
  end)

lemma missing_compl_compl {T : Type} [HfT : fintype T] [Hdeceq : decidable_eq T] (A : finset T) : finset.compl (finset.compl A) = A :=
  begin
    apply eq_of_subset_of_subset,
  apply subset_of_forall,
  intro x HxnnA,
  have  nnxA : x ∉ finset.compl A, from not_mem_of_mem_compl HxnnA,
  rewrite (not_iff_not_of_iff (mem_compl_iff A x)) at nnxA,
  exact (not_not_elim nnxA),
  apply subset_of_forall,
  intro x HxA,
  apply mem_compl,
  rewrite (not_iff_not_of_iff (mem_compl_iff A x)),
  apply not_not_intro,
  exact HxA
  end

lemma eq_is_eq_compl {T : Type} [HfT : fintype T] [Hdeceq : decidable_eq T] {A B : finset T} : (A = B) ↔ (- A = - B) :=
  begin
    apply iff.intro,
    intro HAB,
    rewrite HAB,
    intro HcAcB,
    rewrite -missing_compl_compl,
    rewrite HcAcB,
    apply missing_compl_compl
  end


lemma image_id {T : Type} [HfT : fintype T] [Hdeceq : decidable_eq T] {A : finset T} : id ' A = A := ext (take a, iff.intro (suppose Ha : a ∈ id ' A,
  begin
  rewrite mem_image_iff at Ha,
  cases Ha with x Hx,
  cases Hx with HxA Hxa,
  rewrite ↑id at Hxa,
  exact (eq.subst Hxa HxA)
  end)
  (suppose a ∈ A,
    begin
    rewrite mem_image_iff,
    apply (exists.intro a),
    exact and.intro this rfl
    end))

-- less sure that the next two are really necessary

lemma image_singleton {A B : Type} [hA: decidable_eq A] [hB: decidable_eq B] (f : A → B) (a : A) :
image f (insert a empty) =  insert (f a) empty :=
begin
rewrite image_insert
end

lemma singleton_subset_iff {A : Type} [hA: decidable_eq A] (a : A) (S : finset A) : '{a} ⊆ S ↔ a ∈ S :=
  iff.intro (take H, mem_of_subset_of_mem H (mem_singleton a))
  (take HaS,
  begin
  apply subset_of_forall,
  intro x Hx, rewrite mem_singleton_iff at Hx,
  rewrite Hx, exact HaS
  end)

lemma insert_empty {A : Type} [hAdec : decidable_eq A] (a : A) (b : A) :
finset.insert a finset.empty = insert b empty → a = b :=
assume Heq_set,
have Hab : mem a (insert b empty), from (eq.subst Heq_set (mem_insert a empty)),
or.elim (eq.subst (mem_insert_eq a b empty) Hab) (take H, H)
begin
intro Habs,
exact false.elim (not_mem_empty a Habs)
end

lemma subset_sep_iff {A : Type} [fintype A] [decidable_eq A] (p1 p2 : A → Prop) [decidable_pred (λ x, p1 x)] [decidable_pred (λ x, p2 x)] : {x ∈ univ | p1 x} ⊆ {x ∈ univ | p2 x} ↔ ∀ (x : A), p1 x → p2 x :=
begin
 apply iff.intro,
 intro Hp1p2,
 intro x Hp1x,
 have Hsepp1x : x ∈ sep p1 univ, from mem_sep_of_mem (mem_univ _) Hp1x,
 have Hp2x : x ∈ sep p2 univ, from mem_of_subset_of_mem Hp1p2 Hsepp1x,
 exact (of_mem_sep Hp2x),
 intro Hp1p2,
 have H : ∀ (x : A), x ∈ {x ∈ univ | p1 x} → x ∈ { x ∈ univ | p2 x}, from
 take x Hx, begin apply mem_sep_of_mem (mem_univ _), apply Hp1p2 x (of_mem_sep Hx) end,
 apply subset_of_forall H
end

end set_operations

section finset_of_fintype

definition fintype_of_finset [instance] {T : Type} [HfT : fintype T] : fintype (finset T) := fintype.mk sorry sorry sorry

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

definition smallest (P : nat → Prop) (HdecP : forall (n : nat), decidable (P n))
(n : nat) : P n →  exists (m : nat), m ≤ n ∧ P m ∧ ∀ k, P k → m ≤ k :=
  have Hgeneral : ∀ i, i ≤ n → P i → exists (m : nat), m ≤ i ∧ P m ∧ ∀ k, P k → m ≤ k, from nat.rec_on n
  begin
  intro i li0 HPi,
  apply (exists.intro 0),
  rewrite (eq_zero_of_le_zero li0) at *,
  apply and.intro,
  apply nat.le_refl,
  apply (and.intro HPi),
  intro k Hk,
  apply zero_le
  end
  begin
  intro a HR,
  have Hcases : (exists j, j ≤ a ∧ P j) ∨ ¬ (exists j, j ≤ a ∧ P j), from (decidable.em (exists j, j ≤ a ∧ P j)),
  cases Hcases with yes no,
  cases yes with j Hj,
  cases Hj with lja Pj,
  intro i Hi HPi,
  cases (le_or_eq_succ_of_le_succ Hi) with lia iSa,
  apply (HR i lia HPi),
  cases (le_or_gt i j) with lij ltji,
  apply (HR i (nat.le_trans lij lja) HPi),
  cases (HR j lja Pj) with m Hm,
  apply (exists.intro m),
  apply and.intro,
  apply (nat.le_of_lt (lt_of_le_of_lt (and.left Hm) ltji)),
  exact (and.right Hm),
  intro i liSa HPi,
  cases (le_or_eq_succ_of_le_succ liSa) with lia iSa,
  exfalso, apply no,
  apply exists.intro i (and.intro lia HPi),
  apply exists.intro i,
  apply and.intro,
  apply nat.le_refl,
  apply and.intro,
  exact HPi,
  intro k Pk,
  cases nat.lt_or_ge k i with ltki geki,
  exfalso, apply no,
  apply exists.intro k,
  apply and.intro,
  apply le_of_lt_succ,
  apply lt_of_lt_of_le ltki liSa,
  exact Pk,
  exact geki
  end,
  Hgeneral n !le.refl


lemma minSet_exists (P : finset T → Prop) (HdecP : forall (A : finset T), decidable (P A)) (C : finset T) (HPC : P C) :
  exists A, minSet P A ∧ subset A C :=
  let Pnat := λ (n  :nat), exists (B : finset T), card B = n ∧ P B ∧ B ⊆ C in
  have HPnatC : Pnat (card C), from exists.intro C (and.intro rfl (and.intro HPC (subset.refl C))),
  have Hsmallest : exists (m : nat), m ≤ (card C) ∧ Pnat m ∧ ∀ k, Pnat k → m ≤ k,
  from @smallest T _ _ Pnat (λ n, decidable_exists_finite) (card C) HPnatC,
  obtain m Hm, from Hsmallest,
  begin
  cases Hm with Hmcard Hm2,
  cases Hm2 with HPnatm Hminm,
  cases HPnatm with B HB,
  apply (exists.intro B),
  apply and.intro,
  intro K,
  intro HsKB,
  apply iff.intro,
  intro HPK,
  apply eq_of_card_eq_of_subset,
  have HcardKB : card K ≤ card B, from card_le_card_of_subset HsKB ,
  have cardBK : card B ≤ card K, from
  begin
    rewrite (and.left HB),
    apply ((Hminm (card K))),
    apply (exists.intro K),
    apply and.intro,
    apply rfl,
    apply and.intro,
    exact HPK,
    apply (subset.trans HsKB (and.right (and.right HB))),
  end,
  apply (eq_of_le_of_ge HcardKB cardBK),
  exact HsKB,
  intro Heq, rewrite Heq, exact (and.left(and.right HB)),
  exact and.right (and.right HB)
  end

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
  have Hsub : - B ⊆ - A, from subset_compl HsAB,
  have H : _, from minsetinf (λ B, P (- B)) (- A) (- B) Hmax (eq.substr (missing_compl_compl B) HPB) Hsub,
  begin
   rewrite -(missing_compl_compl),
   rewrite H, apply missing_compl_compl
  end

lemma maxSet_exists (P : finset T → Prop) [HdecP : forall A, decidable (P A)](C : finset T) (HPC : P C) :
  exists A, maxSet P A ∧ subset C A :=
  have H : _,  from minSet_exists (λ B, P (compl B)) _ (compl C) (eq.substr (missing_compl_compl C) HPC),
  obtain A HA, from H,
  exists.intro (compl A)
  (and.intro
  (eq.substr (missing_compl_compl A) (and.left HA))
  begin
  rewrite -missing_compl_compl,
  apply subset_compl,
  exact and.right HA
  end)

lemma maxSet_iff {P : finset T → Prop} {A : finset T} : maxSet P A ↔ (∀ B, A ⊆ B → (P B ↔ B = A)) :=
  begin
    rewrite [↑maxSet,↑minSet],
    apply iff.intro,
    intro H1,
    intro B HB,
    have scBcA : - B ⊆ - A, from subset_compl HB,
    have H : P B ↔ - B = - A, from eq.subst !missing_compl_compl (H1 (-B) (scBcA)),
    rewrite [H,-eq_is_eq_compl],
    intro H2,
    intro B HBcA,
    have sAcB : A ⊆ - B, from eq.subst !missing_compl_compl (subset_compl HBcA),
    have HcBA : (P (-B) ↔ - B = A), from (H2 (-B) sAcB),
    rewrite [HcBA,eq_is_eq_compl,missing_compl_compl]
  end

end minmax
