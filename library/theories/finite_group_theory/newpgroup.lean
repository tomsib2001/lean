import data algebra.group .subgroup .finsubg theories.number_theory.pinat .cyclic .perm .action

open nat finset fintype group_theory subtype

-- useful for debugging
set_option formatter.hide_full_terms false

definition pred_p [reducible] (p : nat) : nat → Prop := λ n, n = p

section set_missing

section finset_of_fintype

lemma subset_inter {T : Type} [Hdeceq : decidable_eq T] {A B C : finset T} :
  A ⊆ B → A ⊆ C → A ⊆ B ∩ C := sorry

lemma finset_inter_subset_left {T : Type} [Hdeceq : decidable_eq T] {A B  : finset T} :
  A ∩ B ⊆ A := sorry

lemma finset_inter_subset_right {T : Type} [Hdeceq : decidable_eq T] {A B  : finset T} :
  A ∩ B ⊆ B := sorry

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

-- why is this hard to prove?
lemma missing_compl_compl (A : finset T) : finset.compl (finset.compl A) = A :=
  sorry

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

end set_missing

section groupStructure

definition is_finsubg_prop [class] (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] (A : finset G) : Prop :=
  1 ∈ A ∧ finset_mul_closed_on A ∧ finset_has_inv A

attribute is_finsubg_prop [reducible]

definition is_finsubg_is_finsubg_prop {G : Type} [ambientG : group G]
[deceqG : decidable_eq G] {A : finset G} : is_finsubg_prop G A → is_finsubg A :=
  assume H,
  is_finsubg.mk (and.left H) (and.left (and.right H)) (and.right (and.right H))

structure Fin_subg (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] := (carrier : finset G) (struct : is_finsubg_prop G carrier)

attribute Fin_subg.carrier [coercion] [reducible]
attribute Fin_subg.struct [instance] [reducible]

lemma struct_irrelevant (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] (H : finset G) (fsg1 : is_finsubg_prop G H) (fsg2 : is_finsubg_prop G H) :
  fsg1 = fsg2 := rfl

lemma injective_projection (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] -- (H1 H2 : Fin_subg G)
:
  function.injective (@Fin_subg.carrier G ambientG deceqG) :=
  take (H2 : Fin_subg G) (H1 : Fin_subg G),
  Fin_subg.rec_on H1 (Fin_subg.rec_on H2
  (take c1 p1 c2 p2 Heq,
  begin
   have Heqc : c1 = c2, from Heq,
   clear Heq,
   revert p1,
   rewrite Heqc,
   intro p1,
   reflexivity
  end
  ))

lemma finSubGroups [instance] (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] : fintype (Fin_subg G) := sorry

example : ∀ (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] , decidable (∀ (H : Fin_subg G), 1 ∈ H) :=
take G aG decG,
  decidable_forall_finite

definition subgroup (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] := { S : finset G | is_finsubg_prop G S }

definition is_fin_subg_in_all_subgroups [instance] {G : Type} [ambientG : group G]
[deceqG : decidable_eq G] (S : subgroup G) : is_finsubg (elt_of S) :=
  is_finsubg_is_finsubg_prop (has_property S)

end groupStructure

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
  have H1 : x = 1,
  from eq_of_mem_singleton Hx,
  rewrite H1,
  exact finsubg_has_one A
  end

lemma card1 : card ('{(1:G)}) = 1 :=
  calc
  card ('{(1:G)}) = card (empty) + 1 : card_insert_of_not_mem (!not_mem_empty)
  ...             = 0 + 1 : {card_empty}
  ...             = 1 : nat.add_zero

lemma lmul_one_id (x : G) : lmul_by x 1 = x :=
calc
  lmul_by x 1 = (λ y, x * y) 1 : rfl
  ...         = (x * 1)        : rfl
  ...         = x              : !mul_one

local attribute finset_has_inv [reducible]

lemma decidable_is_finsubg_prop [instance] {A : finset G} : decidable (is_finsubg_prop G A) := _

reveal decidable_is_finsubg_prop

lemma lagrange_div {H1 H2 : finset G} [H1gr : is_finsubg H1] [ H2gr : is_finsubg H2]
  (HS : subset H1 H2) :
  card H1 ∣ card H2 :=
  dvd_of_eq_mul _ _ _ (eq.subst !nat.mul_comm (lagrange_theorem HS))

end groups_missing

section PgroupDefs

parameter pi : ℕ → Prop
variable [Hdecpi : ∀ p, decidable (pi p)]

definition pgroup [reducible] (H : finset G) := is_pi_nat pi (card H)

include Hdecpi
lemma decidable_pigroup [instance] (H : finset G) : decidable (pgroup H) :=
  begin
   apply decidable_pi
  end

reveal decidable_pigroup

omit Hdecpi

-- the index of the subgroup A inside the group B
definition index [reducible] (A B : finset G) -- (Psub : finset.subset A B)
:= finset.card (fin_lcosets A B)

definition pi_subgroup [reducible] (H1 H2 : finset G) := subset H1 H2 ∧ pgroup H1

include Hdecpi

definition decidable_pi_subgroup [instance] (H1 H2 : finset G) : decidable (pi_subgroup H1 H2) := _

reveal decidable_pi_subgroup

omit Hdecpi

definition pi_elt (pi : ℕ → Prop) (x : G) : Prop := is_pi_nat pi (order x)

definition Hall [reducible] (A B : finset G) :=
subset A B ∧ coprime (card A) (index A B)

include Hdecpi

lemma pgroup_dec (H : finset G) : decidable (pgroup H) := _

definition pHall [reducible] (A B : finset G) :=
subset A B ∧ pgroup A ∧ is_pi'_nat pi (index A B)

end PgroupDefs

section sylows

-- the set of p-Sylows of a subset A
definition Syl [reducible] (p : nat) (A : finset G) :=
{ S ∈ finset.powerset A | is_finsubg_prop G S ∧ pHall (pred_p p) S A }

-- Definition Sylow A B := p_group B && Hall A B.
definition is_sylow p (A B : finset G) := pgroup (pred_p p) A ∧ Hall A B ∧ is_finsubg_prop G A

definition is_in_Syl [class] (p : nat) (A S : finset G) := S ∈ Syl p A

end sylows

lemma pi_subgroup_trans {pi} {H1 H2 H3 : finset G} : pi_subgroup pi H1 H2 → subset H2 H3 → pi_subgroup pi H1 H3 :=
assume Hpi12 Hs23,
  and.intro
  (subset.trans (and.left Hpi12) Hs23)
  (and.right Hpi12)

lemma pi_subgroup_sub {pi} {H1 H2 H3 : finset G} : pi_subgroup pi H1 H3 → subset H1 H2 → subset H2 H3 → pi_subgroup pi H1 H2 :=
  assume Hpi1 s12 s23,
  and.intro
  s12
  (and.right Hpi1)

lemma pgroup_card (p : nat) (H : finset G) : pgroup (pred_p p) H → exists n, card H = p^n :=
  assume Hpgroup,
  sorry

lemma Hall_of_pHall (pi : ℕ → Prop) [Hdecpi : ∀ p, decidable (pi p)] (A B : finset G) : pHall pi A B → Hall A B :=
  assume HpHall : pHall pi A B,
  (and.intro (and.left HpHall)
  (
    have H_pi_A : is_pi_nat pi (card A), from and.left (and.right HpHall),
    have H_pi'_indAB : is_pi'_nat pi (index A B), from and.right (and.right HpHall),
    coprime_pi_pi' H_pi_A H_pi'_indAB
  ))


lemma equiv_Syl_is_Syl p (S A : finset G) : S ∈ Syl p A ↔ is_sylow p S A :=
  iff.intro
  (assume Hmem,
  have HS : is_finsubg_prop G S ∧ pHall (pred_p p) S A, from of_mem_sep Hmem,
  and.intro
  (and.left (and.right(and.right HS)))
  (and.intro
  (Hall_of_pHall (pred_p p) S A (and.right HS))
  (and.left HS)
  )
  )
  (assume H_syl,
  have H1 : is_pi_nat (pred_p p) (card S), from and.left H_syl,
  have H2 :(subset S A ∧ coprime (finset.card S) (index S A)), from (and.left (and.right H_syl)),
  have H3 : is_finsubg_prop G S, from and.right (and.right H_syl),
  mem_sep_of_mem
  (mem_powerset_of_subset (and.left H2))
  (
  have Hsub : subset S A, from and.left H2,
  have Hpgroup : pgroup (pred_p p) S, from H1,
  have Hpi' : is_pi'_nat (pred_p p) (index S A), from pi_pi'_coprime H1 (and.right H2),
  and.intro H3 (and.intro Hsub (and.intro Hpgroup Hpi')))
  )

lemma sylow_finsubg_prop [instance] (p : nat) (A : finset G) (S : finset G)  [HSyl : is_in_Syl p A S] : is_finsubg_prop G S :=
  and.left (of_mem_sep HSyl)

reveal is_finsubg_is_finsubg_prop

definition sylow_is_finsubg [instance] (p : nat) (A S : finset G) [HSyl : is_in_Syl p A S] : is_finsubg S
:= is_finsubg_is_finsubg_prop (sylow_finsubg_prop p A S)

lemma syl_is_max_pgroup (p : nat) (A S : finset G) : is_in_Syl p A S ↔ maxSet (λ B, pgroup (pred_p p) B) S :=
  iff.intro
  (assume HSyl,
  iff.elim_right (maxSet_iff -- (λ B, pgroup (pred_p p) B) S
  )
  (take B HSB,
   iff.intro
   (sorry)
   (sorry)))
  (sorry)

example (p : nat) (A S : finset G) (H : is_in_Syl p A S)
: is_finsubg S := _ -- @sylow_is_finsubg G _ _ _ p A S H  --(sylow_is_finsubg _)

section action_by_conj

definition conj_subsets : G → group_theory.perm (finset G) :=
  λ (g : G), perm.mk (λ H, image (conj_by g) H)
  (take H1 H2,
    sorry -- should be easy
  )

-- lemma tr_conj_subsets (A S1 S2 : finset G):  exists (g : G), @perm.f (conj_subsets g) S1 = S2 := sorry

-- let us try to define the action of G by conjugation on a subset

-- definition action_by_conj (A : finset G) [Hsubg : is_finsubg A] (a : A) : perm A :=
--   take b, lmul_by a (rmul_by a⁻¹ b)

end action_by_conj

-- only true if they actually are groups
lemma pgroupS {pi : ℕ → Prop} {H1 H2 : finset G} [H1gr : is_finsubg H1] [ H2gr : is_finsubg H2] :
  subset H1 H2 → pgroup pi H2 → pgroup pi H1 :=
    assume HS HpiH2,
   pinat_dvd (lagrange_div HS) HpiH2

lemma pisubgroupS {pi : ℕ → Prop} (H2 : finset G) {H1 H3 : finset G}
      [H1gr : is_finsubg H1] [ H2gr : is_finsubg H2] (HS : subset H1 H2) :
      pi_subgroup pi H2 H3 → pi_subgroup pi H1 H3 :=
      assume Hpi23,
      and.intro
      (subset.trans HS (and.left Hpi23))
      (pgroupS HS (and.right Hpi23))

-- lemma lcoset_one (B : finset G): (fin_lcosets B '{(1:G)}) = insert (fin_lcoset B 1) empty :=
-- let f := (λ x, fin_lcoset B x) in
--   image_singleton f


lemma inj_fin_lcoset_one -- (B : finset G)
: function.injective (fin_lcoset '{(1:G)}) :=
take (x : G) (a : G),
assume Hxa,
have H1 : ∀ (x : G), fin_lcoset (insert (1 : G) empty) x = image (lmul_by x) (insert 1 empty), from take (x : G), rfl,
have H2 : ∀ (x : G), image (lmul_by x) (insert (1 : G) empty) = insert (lmul_by x (1:G)) empty , from take x, begin
apply image_singleton
end,
have H : ∀ (x : G),  fin_lcoset (insert (1 : G) empty) x = insert (lmul_by x 1) empty, from take x,
calc
   fin_lcoset (insert (1 : G) empty) x = image (lmul_by x) (insert 1 empty) : {H1 x}
   ...                                 = insert (lmul_by x 1) empty         : {H2 x},
have Hx : fin_lcoset (insert (1 : G) empty) x = insert (lmul_by x 1) empty, from (H x),
have Ha : fin_lcoset (insert (1 : G) empty) a = insert (lmul_by a 1) empty, from (H a),
have showdown : insert (lmul_by x 1) empty =  insert (lmul_by a 1) empty, from eq.subst Hx (eq.subst Ha Hxa),
insert_empty x a (eq.subst (lmul_one_id x) (eq.subst (lmul_one_id a) showdown))

lemma index_one (B : finset G)  : index '{(1:G)} B = finset.card B :=
  calc
  index '{(1:G)} B = finset.card (fin_lcosets '{(1:G)}  B) : rfl
  ...              = finset.card (image (fin_lcoset '{(1:G)}) B) : rfl
-- problem here : fin_lcoset '{(1:G)} has type G → finset G instead of
-- B → finset G
  ...              = finset.card B : sorry --(card_eq_card_image_of_inj (inj_fin_lcoset_one))
  ...              = _ : sorry

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



section sylowTheorem

parameter {p : nat}
variable A : finset G
variable [HAfG : is_finsubg A]

-- for this definition to be interesting, we need to be able to talk about the group generated by H : finset G
-- this may be done later but is not urgent
-- definition maxGroup [reducible] (P : subgroup G → Prop) [HdecP : ∀ B, decidable (P B)] (H : finset G) : Prop :=
--   maxSet (λ (B : finset) ,

-- pose maxp A P := [max P | p.-subgroup(A) P];
definition maxp [reducible] (P : finset G) : Prop := maxSet (λ (B : finset G), pi_subgroup (pred_p p) B A ∧ is_finsubg_prop G B) P

-- lemma maxp_refl (P : finset G) : maxp A P → pi_subgroup (pred_p p) P A ∧ is_finsubg_prop G P :=
--   assume (Hmaxp : maxp A P),
--   maxsetp Hmaxp

-- TODO : extend to maxgroup (see fingroup.v)

definition maxp_is_finsubg [instance] (P : finset G) [Hmaxp : maxp A P] : is_finsubg P
:= have H : is_finsubg_prop G P, from and.right (maxsetp Hmaxp), is_finsubg_is_finsubg_prop H

definition decidable_maxp [instance] (P : finset G) : decidable (maxp A P) :=
decidable_maxset (λ B, pi_subgroup (pred_p p) B A ∧ is_finsubg_prop G B) P

-- reveal decidable_maxp
-- pose S := [set P | maxp G P].

definition S := { P : subgroup G | maxp A (elt_of P) }

-- S A is a fintype because it is a subtype of a subtype of a fintype. There seem to be no instances of this yet
definition finTSA [instance] : fintype (S A) := sorry


-- definition S := subtype (maxp A)

-- definition f : G → S → S := sorry

abbreviation normalizer_in [reducible] (S T : finset G) : finset G := T ∩ normalizer S

-- SmaxN P Q: Q \in S -> Q \subset 'N(P) -> maxp 'N_G(P) Q.
-- reminder: 'N(P) = the normalizer of P, 'N_G(P) = the normalizer of P in G
lemma SmaxN (P Q : finset G) : maxp A Q → Q ⊆ normalizer P → maxp (normalizer_in P A) Q :=
  assume (HmaxP : maxp A Q) HQnormP,
  iff.elim_right (maxSet_iff)
  (take B HQB,
  have H : _, from iff.elim_left (maxSet_iff) HmaxP B HQB,
  iff.intro
  (assume H1,
  begin
  apply (iff.elim_left H),
  apply and.intro,
  apply pi_subgroup_trans (and.left H1),
  exact (finset_inter_subset_left),
  exact (and.right H1)
  end)
  (assume Heq,
  begin
  have pi_subgroup (pred_p p) B A ∧ is_finsubg_prop G B, from iff.elim_right H Heq,
  apply and.intro,
  have Hsub : B ⊆ (A ∩ (normalizer P)),
  from (subset_inter (and.left (and.left this)) ((eq.symm Heq) ▸ HQnormP)),
  apply (pi_subgroup_sub (and.left this) Hsub),
  exact finset_inter_subset_left,
  exact and.right this
  end))

-- !!!!!!!! strange : Lean refuses to acknowledge the existence of is_normal_in from group_theory
-- Definition normal A B := (A \subset B) && (B \subset normaliser A).
definition is_normal_in (B C : finset G) : Prop := B ⊆ C ∧ B ⊆ (normalizer A)

-- lemma normSelf (A : finset G) : A ⊆ (normalizer A) :=
--   subset_normalizer

include HAfG

-- have nrmG P: P \subset G -> P <| 'N_G(P).
lemma nrmG (P : finset G) [HfGP : is_finsubg P] : P ⊆ A → is_normal_in A P (normalizer_in P A) :=
  assume sPA,
  and.intro
  (subset_inter sPA (subset_normalizer))
  (subset.trans sPA (subset_normalizer))

omit HAfG

-- (in pgroup.v) Lemma normal_max_pgroup_Hall G H :
--   [max H | pi.-subgroup(G) H] -> H <| G -> pi.-Hall(G) H.
-- let us do a less general version for starters
lemma normal_max_pgroup_Hall (B C : finset G) : maxp C B → is_normal_in A B C → pHall (pred_p p) B C := assume HmaxB Hnormal,
  have HB : (pi_subgroup (pred_p p) B C) ∧ is_finsubg_prop G B, from maxsetp HmaxB,
  and.intro (and.left Hnormal)
  (and.intro (and.right (and.left HB))
  (have toto : _, from and.right (and.left HB),
  sorry -- here we need a complicated argument explaining that if p divides [C : B],
  --B was not maximal
  )
  )

-- have sylS P: P \in S -> p.-Sylow('N_G(P)) P.
lemma sylS (P : finset G) : maxp A P → is_sylow p P (normalizer_in P A) :=
  assume HmaxP,
  sorry

local attribute perm.f [coercion]

check λ g, action_by_conj_on_finsets g
print subtype.tag

definition pre_conjG (g : G) (s : (S A)) : finset G := (action_by_conj_on_finsets g (elt_of (elt_of s)))

lemma pre_conjG_in_S (g : G) (s : S A) : maxp A (pre_conjG A g s) :=
   have HmaxS : maxp A (elt_of (elt_of s)), from has_property s,
   begin
     apply (iff.elim_right maxSet_iff),
     intro B HsB,
     apply iff.intro,
     apply sorry,
     apply sorry
   end
 -- (λ (B : finset G), pi_subgroup (pred_p p) B A ∧ is_finsubg_prop G B) A
   -- (pre_conjG A g s)

definition conjG_hom (g : G) (s : S A) : _ := tag (pre_conjG A g s) (pre_conjG_in_S A g s)

-- definition conjG (g : G) : perm (S A) := perm.mk (λ s, action_by_conj_on_finsets g s) (action_by_conj_on_finsets_inj)

-- -- have{SmaxN} defCS P: P \in S -> 'Fix_(S |'JG)(P) = [set P].
-- lemma defCS (P : finset G) : maxp A P → fixed_points conjG (S A) = insert P empty := sorry

end sylowTheorem
