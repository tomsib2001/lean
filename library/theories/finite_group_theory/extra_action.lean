import algebra.group data theories.finite_group_theory.hom theories.finite_group_theory.perm theories.finite_group_theory.finsubg theories.finite_group_theory.action data.finset.extra_finset

-- namespace group_theory
open finset function perm group_theory

local attribute perm.f [coercion]

section conjugation_action

section missing

lemma injective_image {A B : Type} [HdeceqB : decidable_eq B] (f : A → B) (Hinjf : injective f) : injective (image f : finset A → finset B) :=
  assume s1 s2 Heqfs1s2,
  eq_of_subset_of_subset
  (subset_of_forall
    (take x Hxs1,
    have Hfx : f x ∈ f ' s2, from eq.subst Heqfs1s2 (mem_image_of_mem f Hxs1),
    obtain x2 (Hx2 : x2 ∈ s2 ∧ f x2 = f x), from eq.subst (mem_image_eq f) Hfx,
    have Heq : x2 = x, from Hinjf (and.right Hx2),
    eq.subst Heq (and.left Hx2)
    ))
  (subset_of_forall
  (
  take x Hxs2,
    have Hfx : f x ∈ f ' s1, from eq.substr Heqfs1s2 (mem_image_of_mem f Hxs2),
    obtain x1 (Hx1 : x1 ∈ s1 ∧ f x1 = f x), from eq.subst (mem_image_eq f) Hfx,
    have Heq : x1 = x, from Hinjf (and.right Hx1),
    eq.subst Heq (and.left Hx1)
  ))

end missing

variables {G : Type} [Hgr : group G] [ Hft : fintype G]
include Hgr Hft

definition action_by_conj : G → perm G :=
take g, perm.mk (conj_by g) (conj_inj g)

variable [Hdec : decidable_eq G]

include Hdec

lemma conj_by_compose (g1 g2 : G) : conj_by (g1 * g2) = (conj_by g1)∘(conj_by g2) :=
            funext (take x, begin rewrite conj_compose end)

lemma action_by_conj_hom : homomorphic (@action_by_conj G _ _) :=
  take (g1 g2 : G),
eq.symm (calc
 action_by_conj g1 * action_by_conj g2 = perm.mk ((conj_by g1)∘(conj_by g2)) _ : rfl
 ...                                   = perm.mk ((conj_by (g1 * g2))) (conj_inj _) : begin congruence, rewrite conj_by_compose end
 ...                                   =  action_by_conj (g1 * g2) : rfl)

-- lemma action_by_conj_inj : injective (@action_by_conj G _ _) := sorry

-- lemma action_by_conj_is_iso [instance] : is_iso_class (@action_by_conj G _ _) :=
-- is_iso_class.mk action_by_conj_hom action_by_conj_inj


lemma conj_by_im_inj (g : G) : injective (image (conj_by g)) :=
  begin
    apply injective_image,
    exact (conj_inj g)
  end


definition action_by_conj_on_finsets : G → perm (finset G) :=
take g, perm.mk (image (conj_by g)) (conj_by_im_inj g)

lemma action_by_conj_on_finsets_inj : injective (@action_by_conj_on_finsets G _ _) := sorry

lemma conj_by_image_compose (g1 g2 : G) : image (conj_by g1) ∘ image (conj_by g2) = image (conj_by (g1 * g2)) :=
funext (take s,
  begin
  rewrite conj_by_compose,
  rewrite image_comp
 end)

lemma action_by_conj_on_finsets_hom :
  homomorphic (@action_by_conj_on_finsets G Hgr Hft Hdec) :=
  take (g1 g2 : G),
eq.symm (calc
 action_by_conj_on_finsets g1 * action_by_conj_on_finsets g2 = perm.mk ((image (conj_by g1))∘(image (conj_by g2))) _ : rfl
 ...                                   = perm.mk ((image (conj_by (g1 * g2)))) (conj_by_im_inj _) : begin congruence, exact !conj_by_image_compose end
 ...                                   =  action_by_conj_on_finsets (g1 * g2) : rfl)


definition conj_on_finsets_hom [instance] : is_hom_class (@action_by_conj_on_finsets G Hgr Hft Hdec) := is_hom_class.mk action_by_conj_on_finsets_hom

end conjugation_action

section action_by_conj

variables {G : Type} [ambientG : group G] [finG : fintype G] [deceqG : decidable_eq G]
include ambientG deceqG finG

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
