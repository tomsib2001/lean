-- some extra lemmas about group quotients

import data .subgroup .finsubg .extra_finsubg --algebra.group
-- import theories.group_theory.basic

open group_theory finset subtype

namespace group_theory

variables {G : Type} [ambientG : group G] [finG : fintype G] [deceqG : decidable_eq G]
include ambientG deceqG finG

variables (H : finset G) [HfinsubgH : is_finsubg H]
include HfinsubgH
definition quotH := lcoset_type (normalizer H) H

set_option formatter.hide_full_terms false
variable {H}
definition get_lcoset_type (g : G) (HgH : g ∈ normalizer H) : lcoset_type (normalizer H) H :=
(tag (fin_lcoset H g) (exists.intro g (and.intro HgH rfl)))
variable (H)
definition phiH (g : G) : lcoset_type (normalizer H) H := if HgH : g ∈ normalizer H then get_lcoset_type g HgH else fin_coset_one

local attribute fin_lcoset [reducible]

lemma fin_lcosetP g h (HhH : h ∈ H) : g * h ∈ fin_lcoset H g :=
  begin
    rewrite (mem_image_iff (lmul_by g)),
    apply (exists.intro h),
    apply and.intro,
    exact HhH,
    rewrite ↑lmul_by
  end

lemma absorb_H_r g1 g2 h (mg1H : g1 ∈ normalizer H) (mg2H : g2 ∈ normalizer H) (HhH : h ∈ H) : g1 ∈ fin_lcoset H g2 → g1 * h ∈ fin_lcoset H g2 :=
  assume Hg1g2,
  begin
    rewrite (mem_image_iff (lmul_by g2)) at Hg1g2,
    cases Hg1g2 with h Hh,
    cases Hh with Hh Hh1,
    rewrite ↑lmul_by at Hh1,
    rewrite -Hh1,
    rewrite mul.assoc,
    apply fin_lcosetP,
    apply @subg_mul_closed G _ H, --why do we need so much detail?
    exact Hh,
    exact HhH
  end

lemma absorb_H_l g1 g2 h (mg1H : g1 ∈ normalizer H) (mg2H : g2 ∈ normalizer H) (HhH : h ∈ H) : g1 ∈ fin_lcoset H g2 → h * g1 ∈ fin_lcoset H g2 :=
  assume Hg1g2,
  have H1 : h * g1 = g1 * conj_by (g1⁻¹) h, from
  calc
   h * g1 = 1 * (h * g1) : one_mul
  ...     = g1 * g1⁻¹ * (h * g1) : mul.right_inv
  ...     = g1 * (g1⁻¹ * (h * g1)) : mul.assoc
  ...     = g1 * (g1⁻¹ * h * g1) : mul.assoc
  ...     = g1 * (conj_by g1⁻¹ h) : begin rewrite ↑conj_by, rewrite inv_inv end
,
  have H2 : g1⁻¹ ∈ normalizer H, from begin apply normalizer_has_inv, exact mg1H end,
  have H3 : conj_by (g1⁻¹) h ∈ H, from (of_mem_sep H2 h HhH),
  begin
   rewrite H1,
   apply absorb_H_r,
   exact mg1H, exact mg2H,
   exact H3, exact Hg1g2
  end

lemma fin_lcoset_normalizes g1 g2 (Hg2 : g2 ∈ normalizer H) (Hg1 : g1 ∈ fin_lcoset H g2) : g1 ∈ normalizer H :=
begin
apply mem_sep_of_mem, apply mem_univ,
intro h HhH,
rewrite (mem_image_iff (lmul_by g2)) at Hg1,
cases Hg1 with h1 Hh1H, cases Hh1H with Hh1H Hg2h1,
rewrite [-Hg2h1,↑lmul_by,-conj_compose],
apply of_mem_sep Hg2,
apply finsubg_conj_closed,
exact Hh1H, exact HhH
end

lemma phiH_mul_compat (g1 g2 : G) (mg1H : g1 ∈ normalizer H) (mg2H : g2 ∈ normalizer H):
 phiH H (g1 * g2) = (phiH H g1) * (phiH H g2) :=
 have Hg1 : phiH H g1 = get_lcoset_type g1 mg1H, from by apply dif_pos,
 have Hg2 : phiH H g2 = get_lcoset_type g2 mg2H, from by apply dif_pos,
 have mg1g2H : (g1 * g2) ∈ normalizer H, from
 begin apply normalizer_mul_closed, exact mg1H , exact mg2H end,
 have Hg1g2 : phiH H (g1*g2) = get_lcoset_type (g1 *g2) mg1g2H, from by apply dif_pos,
 begin
  rewrite [Hg1, Hg2,  Hg1g2, ↑get_lcoset_type],
  apply tag_eq,
  rewrite ↑[lcoset_mul],
  apply ext, intro a,
  apply iff.intro,
    {
    intro Hag1g2,
    rewrite *mem_Union_iff,
    apply (exists.intro g1),
    rewrite fin_lcoset_compose,
    apply and.intro,
    apply mem_image,
    apply finsubg_has_one,
    apply mul_one,
    exact Hag1g2
    },
    {
    rewrite *mem_Union_iff,
    intro HaUnion,
    cases HaUnion with x Hx,
    cases Hx with Hxg1 Haxg2,
    rewrite -fin_lcoset_compose,
    rewrite (mem_image_iff (lmul_by g1)) at Hxg1,
    cases Hxg1 with h1 Hh1,
    rewrite (mem_image_iff (lmul_by x)) at Haxg2,
    cases Haxg2 with h2 Hh2,
    cases Hh2 with Hh2 Hxh2,
    rewrite mem_image_iff,
    apply (exists.intro (h1 * h2)),
    apply and.intro,
    apply (absorb_H_l H h2 g2),
    apply fin_lcoset_normalizes,
    exact mg2H, exact Hh2,
    exact mg2H,
    exact (and.left Hh1),
    exact Hh2,
    rewrite ↑lmul_by,
    rewrite -mul.assoc,
    cases Hh1 with Hh1H Hxg1h1,
    rewrite ↑lmul_by at Hxg1h1,
    rewrite Hxg1h1,
    rewrite ↑lmul_by at Hxh2,
    exact Hxh2
    }
 end

set_option unifier.max_steps 100000

notation H1 ▸ H2 := eq.subst H1 H2

lemma phiH1 : phiH H 1 = 1 :=
  have P : phiH H 1 = phiH H 1 * phiH H 1, from
  calc
  phiH H 1 = phiH H (1 * 1) : mul_one
  ...      = (phiH H 1) * (phiH H 1) : (phiH_mul_compat H 1 1 normalizer_has_one normalizer_has_one),
  eq.symm (eq.subst (mul.right_inv (phiH H 1)) (mul_inv_eq_of_eq_mul P))

lemma phiH_inv (a : G) (Hanorm : a ∈ normalizer H): phiH H (a⁻¹) = (phiH H a)⁻¹ :=
        have P : phiH H 1 = 1, from phiH1 H,
        have P1 : phiH H (a⁻¹ * a) = 1, from (eq.symm (mul.left_inv a)) ▸ P,
        have P2 : (phiH H a⁻¹) * (phiH H a) = 1, from (phiH_mul_compat H a⁻¹ a (normalizer_has_inv _ Hanorm) Hanorm) ▸ P1,
        have P3 : (phiH H a⁻¹) * (phiH H a) = (phiH H a)⁻¹ * (phiH H a), from eq.symm (mul.left_inv (phiH H a)) ▸ P2,
        mul_right_cancel P3

theorem hom_map_mul_closed (K : finset G) (HKN : K ⊆ normalizer H) : mul_closed_on K → mul_closed_on (phiH H ' K) :=
        assume (Pclosed : mul_closed_on K),
        assume (b1 : lcoset_type (normalizer H) H),
        assume (b2 : lcoset_type (normalizer H) H),
        assume Pb1 : b1 ∈ phiH H ' K, assume Pb2 : b2 ∈ phiH H ' K,
        begin
        rewrite (mem_image_eq (phiH H)) at Pb1,
        rewrite (mem_image_eq (phiH H)) at Pb2,
        cases Pb1 with x1 Hx1, cases Pb2 with x2 Hx2,
        cases Hx1 with Hx1K Hx1b1, cases Hx2 with Hx2K Hx2b2,
        rewrite [-Hx1b1,-Hx2b2],
        have Hx1N : x1 ∈ normalizer H, from mem_of_subset_of_mem HKN Hx1K,
        have Hx2N : x2 ∈ normalizer H, from mem_of_subset_of_mem HKN Hx2K,
        rewrite -(phiH_mul_compat H x1 x2 Hx1N Hx2N),
        apply mem_image,
        apply (Pclosed x1 x2),
        exact Hx1K,
        exact Hx2K,
        apply rfl
        end




-- definition proj (K : (finset G)) : finset (lcoset_type (normalizer H) H) :=
-- all_lcosets (normalizer H) H

-- lemma lift1 (Kbar : finset (finset G)) [HfinsubK : is_finsubg Kbar] :
--   exists (K : finset G) , H ⊆ K ∧ is_finsubg_prop G K -- ∧ (set.map elt_of Kbar = fin_lcosets (normalizer H) K) -- can't even write this down
--   :=
--   have H1inKbar : fin_coset_one ∈ Kbar, from !finsubg_has_one,
--   exists.intro (fin_coset_Union Kbar)
--   (and.intro
--    (iff.elim_right (subset_iff_all _ _) (all_of_forall (take a memaH, iff.elim_right (mem_Union_iff _ _ _)
--   (exists.intro fin_coset_one (and.intro H1inKbar memaH)))))
--    (is_finsubg_prop_is_finsubg _))


lemma lift2 (Kbar : finset (lcoset_type (normalizer H) H)) [HfinsubK : is_finsubg Kbar] :
  exists (K : finset G) , H ⊆ K ∧ is_finsubg_prop G K ∧ (Kbar = fin_lcosets (normalizer H) K) -- can't even write this down
  :=
  have H1inKbar : fin_coset_one ∈ Kbar, from !finsubg_has_one,
  exists.intro (fin_coset_Union Kbar)
  (and.intro
   (iff.elim_right (subset_iff_all _ _) (all_of_forall (take a memaH, iff.elim_right (mem_Union_iff _ _ _)
  (exists.intro fin_coset_one (and.intro H1inKbar memaH)))))
   (is_finsubg_prop_is_finsubg _))


end group_theory
