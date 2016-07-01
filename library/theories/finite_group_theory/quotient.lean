-- some extra lemmas about group quotients

import data theories.finite_group_theory.subgroup theories.finite_group_theory.finsubg theories.finite_group_theory.extra_finsubg --algebra.group
-- import theories.group_theory.basic

import theories.finite_group_theory.extra_hom
open group_theory finset subtype

namespace group_theory

variables {G : Type} [ambientG : group G] [finG : fintype G] [deceqG : decidable_eq G]
include ambientG deceqG finG

variables (H : finset G) [HfinsubgH : is_finsubg H]
include HfinsubgH

definition quotH := lcoset_type (normalizer H) H

set_option formatter.hide_full_terms false
variable {H}

definition get_lcoset_type [reducible] (g : G) (HgH : g ∈ normalizer H) : lcoset_type (normalizer H) H :=
(tag (fin_lcoset H g) (exists.intro g (and.intro HgH rfl)))

variable (H)
definition get_coset_type_alt (K : finset G) : lcoset_type (normalizer H) H :=
if HgH : is_fin_lcoset (normalizer H) H K then tag K HgH else fin_coset_one

lemma gct_altE (K : finset G) (HgH : is_fin_lcoset (normalizer H) H K) : get_coset_type_alt H K = tag K HgH := dif_pos HgH


variable (H)
definition phiH (g : G) : lcoset_type (normalizer H) H :=
if HgH : g ∈ normalizer H then get_lcoset_type g HgH else fin_coset_one

definition psiH [reducible] (g : G) : finset G := fin_lcoset H g

lemma image_psiH (K : finset G) : image (psiH H) K = fin_lcosets H K :=
  rfl

lemma is_fin_lcoset_fin_lcoset (g : G) (HgH : g ∈ normalizer H) :
  (is_fin_lcoset (normalizer H) H (fin_lcoset H g)) :=
  exists.intro g (and.intro HgH rfl)

lemma injective_gct_alt (K : finset G) (HKNH : K ⊆ normalizer H) : set.inj_on (get_coset_type_alt H) (finset.image (psiH H) K) :=
assume L M HL HM Heq,
begin
cases (exists_of_mem_image HL) with l Hl,
cases (exists_of_mem_image HM) with m Hm,
cases Hl with Hl Hpsil,
cases Hm with Hm Hpsim,
have HlNH : l ∈ normalizer H, from mem_of_subset_of_mem HKNH Hl,
have HmNH : m ∈ normalizer H, from mem_of_subset_of_mem HKNH Hm,
have Llcoset : is_fin_lcoset (normalizer H) H L, from exists.intro l (and.intro HlNH Hpsil),
have Mlcoset : is_fin_lcoset (normalizer H) H M, from exists.intro m (and.intro HmNH Hpsim),
rewrite (gct_altE H L Llcoset) at Heq,
rewrite (gct_altE H M Mlcoset) at Heq,
have L = elt_of (tag L Llcoset), from elt_of.tag L Llcoset,
rewrite [this,Heq]
end

lemma psiH_eq_phiH (K : finset G) (HKNH : K ⊆ normalizer H) : image (phiH H) K = (get_coset_type_alt H) ' ((psiH H) ' K) :=
ext
  (take a, iff.intro
  (
  begin
  intro Ha,
  cases (exists_of_mem_image Ha) with k Hk,
  cases Hk with HkK Hphika,
  apply mem_image,
  apply mem_image,
  exact HkK,
  apply rfl,
  rewrite ↑phiH at Hphika,
  have HkNH : k ∈ normalizer H, from mem_of_subset_of_mem HKNH HkK,
  rewrite (dif_pos HkNH) at Hphika,
  rewrite ↑get_coset_type_alt,
  rewrite (dif_pos (is_fin_lcoset_fin_lcoset H k HkNH)) at *,
  rewrite ↑get_lcoset_type at Hphika,
  exact Hphika
  end
  )
  (begin
  intro Ha,
  cases (exists_of_mem_image Ha) with Y HY,
  cases HY with HYpsiK Hgctak,
  cases (exists_of_mem_image HYpsiK) with k Hk,
  cases Hk with HkK HkY,
  apply mem_image,
  exact HkK,
  have HkNH : k ∈ normalizer H, from mem_of_subset_of_mem HKNH HkK,
  rewrite [↑phiH,(dif_pos HkNH),↑get_lcoset_type],
  rewrite ↑get_coset_type_alt at Hgctak,
  rewrite -HkY at Hgctak,
  rewrite (dif_pos (is_fin_lcoset_fin_lcoset H k HkNH)) at Hgctak,
  rewrite -Hgctak
  end))

lemma card_im_phi_lcosets (K : finset G) (HKNH : K ⊆ normalizer H) : card ((phiH H) ' K) = card (psiH H ' K) :=
  begin
   rewrite (psiH_eq_phiH H K HKNH),
   apply card_image_eq_of_inj_on,
   exact (injective_gct_alt _ _ HKNH),
  end

lemma phiHE (g : G) (HgH : g ∈ normalizer H) : phiH H g = get_lcoset_type g HgH := dif_pos HgH

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

-- we can now establish that phiH is a morphism
lemma hom_on_phiH : homomorphic_on (normalizer H) (phiH H) :=
  take a b Ha Hb, (phiH_mul_compat H a b Ha Hb)

lemma is_hom_on_class_phiH [instance] : is_hom_on_class (normalizer H) (phiH H) :=
  is_hom_on_class.mk (hom_on_phiH H)


notation H1 ▸ H2 := eq.subst H1 H2

lemma phiH1 : phiH H 1 = 1 := (hom_on_map_one (normalizer H) _)
  -- have P : phiH H 1 = phiH H 1 * phiH H 1, from
  -- calc
  -- phiH H 1 = phiH H (1 * 1) : mul_one
  -- ...      = (phiH H 1) * (phiH H 1) : (phiH_mul_compat H 1 1 normalizer_has_one normalizer_has_one),
  -- eq.symm (eq.subst (mul.right_inv (phiH H 1)) (mul_inv_eq_of_eq_mul P))

lemma phiH_inv (a : G) (Hanorm : a ∈ normalizer H): phiH H (a⁻¹) = (phiH H a)⁻¹ :=
(hom_on_map_inv (normalizer H) _ a Hanorm)
        -- have P : phiH H 1 = 1, from phiH1 H,
        -- have P1 : phiH H (a⁻¹ * a) = 1, from (eq.symm (mul.left_inv a)) ▸ P,
        -- have P2 : (phiH H a⁻¹) * (phiH H a) = 1, from (phiH_mul_compat H a⁻¹ a (normalizer_has_inv _ Hanorm) Hanorm) ▸ P1,
        -- have P3 : (phiH H a⁻¹) * (phiH H a) = (phiH H a)⁻¹ * (phiH H a), from eq.symm (mul.left_inv (phiH H a)) ▸ P2,
        -- mul_right_cancel P3

set_option pp.implicit false

theorem phiH_map_mul_closed (K : finset G) (HKN : K ⊆ normalizer H) (Pclosed : mul_closed_on K) : mul_closed_on (set.image (phiH H) K) :=
begin
apply (hom_on_map_mul_closed (normalizer H) (phiH H) K),
rewrite -subset_eq_to_set_subset, exact HKN,
exact Pclosed
end
        -- assume (b1 : lcoset_type (normalizer H) H),
        -- assume (b2 : lcoset_type (normalizer H) H),
        -- assume Pb1 : b1 ∈ phiH H ' K, assume Pb2 : b2 ∈ phiH H ' K,
        -- begin
        -- rewrite (mem_image_eq (phiH H)) at Pb1,
        -- rewrite (mem_image_eq (phiH H)) at Pb2,
        -- cases Pb1 with x1 Hx1, cases Pb2 with x2 Hx2,
        -- cases Hx1 with Hx1K Hx1b1, cases Hx2 with Hx2K Hx2b2,
        -- rewrite [-Hx1b1,-Hx2b2],
        -- have Hx1N : x1 ∈ normalizer H, from mem_of_subset_of_mem HKN Hx1K,
        -- have Hx2N : x2 ∈ normalizer H, from mem_of_subset_of_mem HKN Hx2K,
        -- rewrite -(phiH_mul_compat H x1 x2 Hx1N Hx2N),
        -- apply mem_image,
        -- apply (Pclosed x1 x2),
        -- exact Hx1K,
        -- exact Hx2K,
        -- apply rfl
        -- end



theorem phiH_finset_mul_closed_on (K : finset G) (HKN : K ⊆ normalizer H) (Pclosed : finset_mul_closed_on K) : finset_mul_closed_on (finset.image (phiH H) K) :=
  begin
  intro x y Hx Hy,
  rewrite mem_eq_mem_to_set,
  rewrite (to_set_image (phiH H) K),
  apply (hom_on_map_mul_closed (normalizer H) (phiH H) K),
  rewrite -subset_eq_to_set_subset,
  apply HKN,
  intro x1 y1 Hx1 Hy1,
  apply Pclosed,
  exact Hx1, exact Hy1,
  rewrite -(to_set_image (phiH H) K),
  exact Hx,
  rewrite -(to_set_image (phiH H) K),
  exact Hy,
  -- this proof was harder than expected! It is longer than a "by-hand" proof
  end
        -- assume x y Hx Hy,
        -- begin
        -- apply (phiH_map_mul_closed H K HKN),
        -- apply Pclosed,
        -- exact Hx,
        -- exact Hy
        -- end

set_option pp.coercions true

theorem phiH_preserves_groups [instance] (K : finset G) (HKN : K ⊆ normalizer H) [HsgK : is_finsubg K] : is_finsubg (phiH H ' K) :=
  have subgphiK : is_subgroup (phiH H ' K), from begin rewrite (to_set_image (phiH H) K), apply (hom_on_map_subgroup (normalizer H) (phiH H)),
  rewrite -subset_eq_to_set_subset, exact HKN end,
  is_finsubg_subg
  -- begin rewrite (to_set_image (phiH H) K),
--       -- apply (hom_on_map_subgroup (normalizer H) (phiH H) HKN),
-- end
-- -- hom_on_map_subgroup (normalizer H) (phiH H) HKN
-- is_finsubg.mk (mem_image (finsubg_has_one K) (phiH1 _)) (phiH_finset_mul_closed_on H K HKN (take x y, (finsubg_mul_closed K)))
-- (take y Hy,
--   begin
--     rewrite mem_image_iff at Hy,
--     cases Hy with x Hxy,
--     cases Hxy with HxK Hxy,
--     rewrite -Hxy,
--     have HxN : x ∈ normalizer H, from mem_of_subset_of_mem HKN HxK,
--     rewrite -(phiH_inv H x HxN),
--     have HxinvK : x⁻¹∈ K, from finsubg_has_inv _ HxK,
--     apply (mem_image HxinvK),
--     apply rfl
--   end)



local attribute fin_coset_Union [reducible]

-- definition foo C h [sCNH : C ⊆ normalizer H] (E : fin_lcoset C h) : (lcoset_type) := tag

-- example (Kbar : finset (lcoset_type (normalizer H) H)) [HfinsubK : is_finsubg Kbar] (L : finset G) [HfinsubL : is_finsubg L] (HLNH : L ⊆ normalizer H) (HsKbarphiL : Kbar ⊆ phiH H ' L) : (fin_coset_Union Kbar) ⊆ L := sorry

lemma lift_subgroup (Kbar : finset (lcoset_type (normalizer H) H)) [HfinsubK : is_finsubg Kbar] :
  exists (K : finset G) , K = fin_coset_Union Kbar ∧ H ⊆ K ∧ is_finsubg_prop G K ∧ image (phiH H) K = Kbar :=
      have H1inKbar : fin_coset_one ∈ Kbar, from !finsubg_has_one,
      exists.intro (fin_coset_Union Kbar)
      (and.intro rfl (and.intro
      (iff.elim_right (subset_iff_all _ _) (all_of_forall (take a memaH, iff.elim_right (mem_Union_iff _ _ _)
      (exists.intro fin_coset_one (and.intro H1inKbar memaH)))))
      (and.intro (is_finsubg_prop_is_finsubg _)
      begin
       apply finset.subset.antisymm,
       apply subset_of_forall,
       intro sbar Hsbar_im,
       rewrite (mem_image_eq (phiH H)) at Hsbar_im,
       cases Hsbar_im with s Hs, cases Hs with Hsunion Heqphi,
       rewrite mem_Union_eq at Hsunion,
       cases Hsunion with xH HxH,
       cases HxH with HxHKbar HsxH,
       have Hsnorm : s ∈ normalizer H, from
       begin
         apply mem_of_subset_of_mem (lcoset_subset_of_subset _ (subset_normalizer)),
         exact HsxH
       end,
       rewrite (phiHE H s Hsnorm) at Heqphi,
       rewrite -Heqphi,
       have Heq : get_lcoset_type s Hsnorm = xH, from
       begin
         apply subtype.eq,
         rewrite ↑get_lcoset_type,
         have Hlcoset : is_fin_lcoset (normalizer H) H (elt_of xH), from has_property xH,
         rewrite ↑is_fin_lcoset at Hlcoset,
         cases Hlcoset with g Hg,
         rewrite -(and.right Hg) at *,
         rewrite -fin_lcoset_same,
         exact HsxH
       end,
       rewrite Heq,
       exact HxHKbar,
       apply subset_of_forall,
       intro xH HxH,
       have Hlcoset : is_fin_lcoset (normalizer H) H (elt_of xH), from has_property xH,
       rewrite ↑is_fin_lcoset at Hlcoset,
       cases Hlcoset with g Hg,
       have Heq : xH = get_lcoset_type g (and.left Hg), from
       begin
        apply subtype.eq,
        rewrite ↑lcoset_type,
        rewrite -(and.right Hg),
       end,
      rewrite Heq,
      have get_lcoset_type g (and.left Hg) = phiH H g, from
        begin rewrite (phiHE H g (and.left Hg)) end,
      rewrite this,
      have g ∈ fin_coset_Union Kbar, from
      begin
        rewrite mem_Union_iff,
        apply exists.intro xH,
        apply and.intro,
        exact HxH,
        rewrite -(and.right Hg),
        rewrite fin_lcoset_same
      end,
      apply mem_image this,
      apply rfl
      end)))

end group_theory
