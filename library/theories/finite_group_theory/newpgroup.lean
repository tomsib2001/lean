import data algebra.group .subgroup .finsubg theories.number_theory.pinat .cyclic .perm .action

open nat finset fintype group_theory

-- useful for debugging
set_option formatter.hide_full_terms false

definition pred_p [reducible] (p : nat) : nat → Prop := λ n, n = p

section set_missing

section finset_of_fintype

lemma subset_inter {T : Type} [Hdeceq : decidable_eq T] {A B C : finset T} : A ⊆ B → A ⊆ C → A ⊆ B ∩ C := sorry

end finset_of_fintype

section minmax

variables [T : Type] [HfT : fintype T] [Hdeceq : decidable_eq T]

include Hdeceq HfT

definition minSet (P : finset T → Prop) (A : finset T) :=
  ∀ (B : finset T), subset B A → (P B ↔ B = A)

definition decidable_minset [instance] (P : finset T → Prop) [HdecP : ∀ B, decidable (P B)] (A : finset T) : decidable (minSet P A) := sorry

lemma minsetp (P : finset T → Prop) (A : finset T) (HminSet : minSet P A) : P A :=
  iff.elim_right (HminSet A (subset.refl A)) (!rfl)

lemma minset_imp (P1 P2 : finset T → Prop) (A : finset T) :
  (∀ B, P1 B ↔ P2 B) → (minSet P1 A → minSet P2 A) :=
  assume Hequiv,
  assume HP1,
   take B HBA,
   iff.intro
   (assume P2B : P2 B, (iff.elim_left (HP1 B HBA)) (iff.elim_right (Hequiv B) P2B))
   (
   assume Heq : B = A,
   begin
   have HP1A : P1 A, from (minsetp P1 A HP1),
   apply (iff.elim_left (Hequiv B)),
   exact (eq.substr Heq HP1A)
   end
   )

lemma minset_eq (P1 P2 : finset T → Prop) (A : finset T) :
  (∀ B, P1 B ↔ P2 B) → (minSet P1 A ↔ minSet P2 A) :=
  assume Hequiv,
  iff.intro
  (assume HP1, minset_imp P1 P2 A Hequiv HP1)
  (assume HP2, minset_imp P2 P1 A (take B, iff.symm (Hequiv B)) HP2)

lemma minsetinf (P : finset T → Prop) (A B : finset T) (HminSet : minSet P A) (HPB : P B)
(Hsubset : subset B A) : B = A :=
  iff.elim_left (HminSet B Hsubset) HPB

-- it seems unecessary in our case (but not sure)
-- lemma ex_minset (P : finset T → Prop) :  → exists A, P A

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

-- lemma subset_insert_eq_or_strict a (s t : finset T) :
--   s ⊆ (insert a t) ↔ s = insert a t ∨ s ⊆ t :=
--   sorry

-- variables (P : nat → Prop) [HdecP : forall A, decidable (P A)]
-- include HdecP

-- lemma decidable_exminP [instance] (n : nat) : decidable (exists m, m ≤ n ∧ P m ∧ ∀ k, k ≤ n → k < m → ¬ P k) := sorry

definition smallest (P : nat → Prop) [HdecP : forall A, decidable (P A)]
(n : nat)  : P n → exists m, m ≤ n ∧ P m ∧ ∀ k, k ≤ n → k < m → ¬ P k :=
  have Hgeneral : ∀ p, p ≤ n → P p → exists m, m ≤ p ∧ P m ∧ ∀ k, k ≤ n → k < m → ¬ P k, from sorry,
  Hgeneral n (nat.le_refl n)

  -- nat.induction_on n (assume P0, exists.intro 0 (and.intro (zero_le 0) (and.intro P0 (λ k Hkle Hklt, false.elim (iff.elim_left (lt_zero_iff_false k) Hklt)))))
  -- (take n HIN HPn,
  --   if Hex: exists m,  m ≤ n ∧ P m ∧ (∀ (k : nat), k < m → ¬ P k) then
  --     (obtain m Hm, from Hex,
  --       exists.intro m
  --       (and.intro
  --       (le_succ_of_le (and.left Hm))
  --       (and.intro (and.left (and.right Hm))
  --        (take k Hk1 Hk2, and.right (and.right (Hm)) k Hk2))))
  --   else
  --     (exists.intro (succ n)
  --      (and.intro
  --      (nat.le_refl (succ n))
  --      (and.intro
  --      HPn
  --      (take k HlekSn HltkSn, _))))
  -- )

-- definition get_minset : forall (P : finset T → Prop) (C : finset T) (HPC : P C), Prop
-- | get_minset P C HPC := if card C = 0 then true else false

lemma minSet_exists (P : finset T → Prop) [HdecP : forall A, decidable (P A)](C : finset T) (HPC : P C) :
  exists A, minSet P A ∧ subset A C :=
  -- let P1 := λ (n : nat) , exists (A : finset T), finset.card A = n ∧ minSet P A ∧ A ⊆ C in
  -- let n := card C in
  -- have Hdec : ∀ A, decidable ((λ n, ∃ A, card A = n ∧ minSet P A ∧ A ⊆ C) A), from sorry,
  -- let H1 := smallest P1 n (exists.intro C (and.intro (rfl) (and.intro _ _))) in
  sorry


  -- have HC : exists T, subset T C ∧ P T, from exists.intro C (and.intro (!subset.refl) HPC),
  -- have HInd : forall S, (exists T, subset T S ∧ P T) → exists T, minSet P T ∧ subset T S, from
  -- finset.induction
  -- (!helper_lemma)
  -- (take a s (Hnas : ¬ a ∈ s) HIP Hpas,
  --    have decidable (∃ T1, T1 ⊆ s ∧ P T1), from sorry, -- typeclasses anyone?
  --    if Hs : exists T1, subset T1 s ∧ P T1 then
  --      (have Hs1 : exists T1, minSet P T1 ∧ T1 ⊆ s, from HIP Hs,
  --      obtain T1 (Hs2 : minSet P T1 ∧ T1 ⊆ s), from Hs1,
  --      have HT1s : T1 ⊆ s, from and.right Hs2,
  --      have HT1as : T1 ⊆ (insert a s), from
  --      (subset.trans HT1s (subset_insert s a) : T1 ⊆ insert a s),
  --      exists.intro T1
  --        (and.intro
  --          (and.left Hs2)
  --          HT1as))
  --    else
  --      (exists.intro
  --      (insert a s)
  --      (and.intro
  --      (
  --        assume B (HB : subset B (insert a s)),
  --        iff.intro
  --          (assume HPB,_
  --          -- or.elim (iff.elim_left (subset_insert_eq_or_strict a B s) HB)
  --          -- (λ x, x)
  --          -- (assume HBs,
  --          -- have Habsurd : exists T1, T1 ⊆ s ∧ P T1, from
  --          -- exists.intro B (and.intro HBs HPB),
  --          -- absurd Habsurd Hs)
  --          )
  --          (assume Heq,
  --           obtain T1 (HT1), from Hpas,
  --           or.elim
  --             (iff.elim_left (subset_insert_eq_or_strict a T1 s) (and.left HT1))
  --             (
  --             assume Heq1,
  --             have Heq2 : T1 = B, from eq.substr Heq (Heq1),
  --             eq.subst Heq2 (and.right HT1)
  --             )
  --             (assume HT1s : T1 ⊆ s,
  --             have HT : exists T1, minSet P T1 ∧ T1 ⊆ s,
  --             from HIP (exists.intro T1 (and.intro HT1s (and.right HT1))),
  --             have Habsurd : exists T1, T1 ⊆ s ∧ P T1, from
  --             exists.intro T1 (and.intro HT1s (and.right HT1)),
  --             absurd Habsurd Hs
  --             )
  --          )
  --      )
  --      (!subset.refl)
  -- ))
  -- )
  -- ,
  -- (HInd C HC)

definition maxSet (P : finset T → Prop) (A : finset T) :=
  minSet (λ B, P (compl B)) (compl A)

definition decidable_maxset [instance] (P : finset T → Prop) [HdecP : ∀ B, decidable (P B)] (A : finset T) : decidable (maxSet P A) := decidable_minset _ _



lemma maxset_eq (P1 P2 : finset T → Prop) (A : finset T) :
  (∀ B, P1 B ↔ P2 B) → (maxSet P1 A ↔ maxSet P2 A) :=
  begin
  intro HP1P2,
  apply minset_eq,
  intro B,
  apply HP1P2
  end

print compl
print diff

-- why is this hard to prove?
lemma missing_compl_compl (A : finset T) : finset.compl (finset.compl A) = A :=
  sorry
   -- eq_of_subset_of_subset
   -- (subset_of_forall
   -- (take (a : T) Hnna,
   --  have H : _, from set.compl_compl A,
   --  have set.compl (ts A) = compl A, from _,
    -- have Ha : a ∈ compl (compl (ts A)), from Hnna,
    _
   --))
   _
   -- eq_of_subset_of_subset
   -- (subset_of_forall
   -- (take a Hnna,
   --  have Hna : ¬ a ∈ (finset.compl A), from not_mem_of_mem_compl Hnna,
   --  _
   -- )
   -- )
   --  _

lemma maxsetp (P : finset T → Prop) (A : finset T) : maxSet P A → P A :=
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

lemma maxSet_iff (P : finset T → Prop) (A : finset T) : maxSet P A ↔ (∀ B, A ⊆ B → (P B ↔ B = A)) :=
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

-- lemma mem_insert_empty {A : Type} [hA: decidable_eq A] {a x : A} : x ∈ (insert a ∅) → x = a :=
-- !set.eq_of_mem_singleton
--   -- assume Hmem,
--   -- or.elim (eq.subst (mem_insert_eq x a ∅) Hmem)
--   -- (λ x, x)
--   -- begin
--   --   intro Habs,
--   --   exact false.elim (not_mem_empty a Habs)
--   -- end

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

-- -- this is not actually what we want, as G is not necessarily finite
-- structure fingroup [class] (G : Type) extends group G :=
-- [finG : fintype G]

-- structure Fingroup := (carrier : Type) (struct : fingroup carrier)

-- attribute Fingroup.carrier [coercion]
-- attribute Fingroup.struct [instance]

-- -- we can now talk about g : G
-- example (FG : Fingroup) (g : FG) : g * 1  = g := mul_one g

definition is_finsubg_prop [class] (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] (A : finset G) : Prop :=
  1 ∈ A ∧ finset_mul_closed_on A ∧ finset_has_inv A


-- structure fin_subg [class] (G : Type) [ambientG : group G]
-- [deceqG : decidable_eq G] (H : finset G) extends is_finsubg H :=
-- [finG : fintype G]

structure Fin_subg (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] := (carrier : finset G) (struct : is_finsubg_prop G carrier)

attribute Fin_subg.carrier [coercion] [reducible]
attribute Fin_subg.struct [instance] [reducible]

-- of course this does not work, we need to make it apparent that
-- Fin_subg G is a finite type

-- how does Mathcomp do this? It seems that fingrouptype is an extension of fintype,
-- and that {group gT} is an extension of {set gT}

lemma struct_irrelevant (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] (H : finset G) (fsg1 : is_finsubg_prop G H) (fsg2 : is_finsubg_prop G H) :
  fsg1 = fsg2 := rfl

lemma injective_projection (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] -- (H1 H2 : Fin_subg G)
:
  function.injective (@Fin_subg.carrier G ambientG deceqG) :=
  take (H2 : Fin_subg G) (H1 : Fin_subg G),
  -- have foo : Fin_subg.struct H1 = eq.substr Heq (Fin_subg.struct H2), from rfl,
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
--   have H1 : Fin_subg.carrier (Fin_subg.mk c1 p1) = c1, from rfl,
--   have H2 : Fin_subg.carrier (Fin_subg.mk c2 p2) = c2, from rfl,
-- -- have Heqc : c1 = c2, from Heq,
--   eq.subst H1 (eq.subst H2 (_))
  ))

    -- @Fin_subg.rec_on G _ _ (λ x, @Fin_subg.carrier G _ _ H1 = @Fin_subg.carrier G _ _ x → H1 = x) H2 (take c s, _)

lemma finSubGroups [instance] (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] : fintype (Fin_subg G) := sorry

-- definition all_subgroups (G : Type) [ambientG : group G]
-- [deceqG : decidable_eq G] : @finset.univ (finSubGroups G) := sorry

example : ∀ (G : Type) [ambientG : group G]
[deceqG : decidable_eq G] , decidable (∀ (H : Fin_subg G), 1 ∈ H) :=
take G aG decG,
  decidable_forall_finite


-- how can we talk about the set of all (automatically finite) subgroups of FG?


-- definition all_subgroups (G : Fingroup) (H : G) :=
-- { S : G | ∀ x, x ∈ S → x = x }

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

-- definition is_finsubg_prop [class] (A : finset G) : Prop :=
--   1 ∈ A ∧ finset_mul_closed_on A ∧ finset_has_inv A

attribute is_finsubg_prop [reducible]

lemma is_finsub_is_finsubg_prop {A : finset G} : is_finsubg_prop G A → is_finsubg A :=
  assume H,
  is_finsubg.mk (and.left H) (and.left (and.right H)) (and.right (and.right H))

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

-- should we enforce H being a group at this point ? no

definition pgroup [reducible] (H : finset G) := is_pi_nat pi (card H)
-- reveal pgroup
-- print pgroup

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

-- lemma pi_subgroup_trans {H1 H2 H3 : finset G} : pi_subgroup H1 H2 → subset H2 H3 → pi_subgroup H1 H3 := _

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

reveal is_finsub_is_finsubg_prop

definition sylow_is_finsubg [instance] (p : nat) (A S : finset G) [HSyl : is_in_Syl p A S] : is_finsubg S
:= is_finsub_is_finsubg_prop (sylow_finsubg_prop p A S)

lemma syl_is_max_pgroup (p : nat) (A S : finset G) : is_in_Syl p A S ↔ maxSet (λ B, pgroup (pred_p p) B) S :=
  iff.intro
  (assume HSyl,
  iff.elim_right (maxSet_iff (λ B, pgroup (pred_p p) B) S)
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

set_option pp.implicit true

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
-- pose maxp A P := [max P | p.-subgroup(A) P];
definition maxp [reducible] (P : finset G) : Prop := maxSet (λ B, pi_subgroup (pred_p p) B A) P

definition decidable_maxp [instance] (P : finset G) : decidable (maxp A P) :=
decidable_maxset (λ B, pi_subgroup (pred_p p) B A) P

-- reveal decidable_maxp
-- pose S := [set P | maxp G P].

definition S := { P ∈ finset.powerset A | maxp A P}

-- definition f : G → S → S := sorry

abbreviation normalizer_in [reducible] (S T : finset G) : finset G := T ∩ normalizer S

-- SmaxN P Q: Q \in S -> Q \subset 'N(P) -> maxp 'N_G(P) Q.
-- reminder: 'N(P) = the normalizer of P, 'N_G(P) = the normalizer of P in G
lemma SmaxN (P Q : finset G) : maxp A Q → Q ⊆ normalizer P → maxp (normalizer_in P A) Q :=
  assume HmaxP HQnormP,
  iff.elim_right (maxSet_iff _ _)
  (take B HQB,
  have H : _, from iff.elim_left (maxSet_iff _ _) HmaxP B HQB,
  iff.intro
  sorry
  (sorry))

-- !!!!!!!! strange : Lean refuses to acknowledge the existence of is_normal_in from group_theory
-- Definition normal A B := (A \subset B) && (B \subset normaliser A).
definition is_normal_in (B C : finset G) : Prop := B ⊆ C ∧ B ⊆ (normalizer A)

lemma normSelf (A : finset G) : A ⊆ (normalizer A) := sorry

-- have nrmG P: P \subset G -> P <| 'N_G(P).
lemma nrmG (P : finset G) : P ⊆ A → is_normal_in A P (normalizer_in P A) :=
  assume sPA,
  and.intro
  (subset_inter sPA (normSelf P))
  (subset.trans sPA (normSelf A))

-- (in pgroup.v) Lemma normal_max_pgroup_Hall G H :
--   [max H | pi.-subgroup(G) H] -> H <| G -> pi.-Hall(G) H.
-- let us do a more general version for starters
lemma normal_max_pgroup_Hall (B C : finset G) : maxp C B → is_normal_in A B C → pHall (pred_p p) B C := sorry

-- have sylS P: P \in S -> p.-Sylow('N_G(P)) P.
lemma sylS (P : finset G) : maxp A P → is_sylow p P (normalizer_in P A) :=
  assume HmaxP,
  sorry

definition conjG : G → perm G := action_by_conj

-- have{SmaxN} defCS P: P \in S -> 'Fix_(S |'JG)(P) = [set P].
lemma defCS (P : finset G) : maxp A P → fixed_points conjG (S A) = P := sorry

end sylowTheorem
