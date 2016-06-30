import algebra.group theories.finite_group_theory.subgroup theories.finite_group_theory.finsubg
theories.finite_group_theory.cyclic theories.finite_group_theory.perm
theories.finite_group_theory.action
import theories.finite_group_theory.extra_action theories.finite_group_theory.quotient theories.finite_group_theory.extra_finsubg data.finset.extra_finset
import theories.number_theory.pinat
import theories.finite_group_theory.pgroup
open nat finset fintype group_theory subtype

namespace group_theory

-- useful for debugging
set_option formatter.hide_full_terms false

definition pred_p [reducible] (p : nat) : nat → Prop := λ n, n = p

variables {G : Type} [ambientG : group G] [finG : fintype G] [deceqG : decidable_eq G]
include ambientG deceqG finG

section pgroup_missing

-- the Cauchy theorem from pgroup only mentions the ambient group..
lemma actual_Cauchy_theorem (H : finset G) [HsgH : is_finsubg H] {p : nat} :
  prime p → p ∣ card H → ∃ h : G, h ∈ H ∧ order h = p := sorry

end pgroup_missing

section PgroupDefs

parameter pi : ℕ → Prop
variable [Hdecpi : ∀ p, decidable (pi p)]

definition pgroup [reducible] (H : finset G) := is_pi_nat pi (card H)

definition pi_subgroup [reducible] (H1 H2 : finset G) := subset H1 H2 ∧ pgroup H1

definition pi_elt (pi : ℕ → Prop) (x : G) : Prop := is_pi_nat pi (order x)

definition Hall [reducible] (A B : finset G) :=
subset A B ∧ coprime (card A) (index A B)

definition pHall [reducible] (A B : finset G) :=
subset A B ∧ pgroup A ∧ is_pi'_nat pi (index A B)

-- decidability on prgroup theory

include Hdecpi

definition pgroup_dec [instance] (H : finset G) : decidable (pgroup H) := _

definition decidable_pigroup [instance] (H : finset G) : decidable (pgroup H) :=
  begin
   apply decidable_pi
  end

definition decidable_pi_subgroup [instance] (H1 H2 : finset G) : decidable (pi_subgroup H1 H2) := _

-- end decidability on prgroup theory

-- some useful lemmas

lemma pi_subgroup_subset {H1 H2 : finset G} (Hpisubg : pi_subgroup H1 H2) : subset H1 H2 :=
  and.left Hpisubg

lemma pi_subgroup_pgroup {H1 H2 : finset G} (Hpisubg : pi_subgroup H1 H2) : pgroup H1 :=
  and.right Hpisubg

end PgroupDefs


section Sylows

-- the set of p-Sylows of a subset A
-- this definition is not the one we want to manipulate in the Sylow theorem,
-- because it is more convenient to have G act on the set of maximal p-subgroups
-- until we prove that those are the two same things

definition Syl [reducible] (p : nat) (A : finset G) :=
{ S ∈ finset.powerset A | is_finsubg_prop G S ∧ pHall (pred_p p) S A }

-- Definition Sylow A B := p_group B && Hall A B.
definition is_sylow p (A B : finset G) := pgroup (pred_p p) A ∧ Hall A B ∧ is_finsubg_prop G A

definition is_in_Syl [class] (p : nat) (A S : finset G) := S ∈ Syl p A

end Sylows

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

definition sylow_finsubg_prop [instance] (p : nat) (A : finset G) (S : finset G)  [HSyl : is_in_Syl p A S] : is_finsubg_prop G S :=
  and.left (of_mem_sep HSyl)

definition sylow_is_finsubg [instance] (p : nat) (A S : finset G) [HSyl : is_in_Syl p A S] : is_finsubg S
:= is_finsubg_is_finsubg_prop (sylow_finsubg_prop p A S)

-- probably a bit soon to show this..
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

-- TODO: there is probably a one-liner proof of this one somewhere, look for it
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

section SylowTheorem


end SylowTheorem

end group_theory
