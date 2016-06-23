/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Author : Haitao Zhang
-/
import algebra.group data .hom .perm .finsubg

namespace group_theory
open finset function

local attribute perm.f [coercion]

private lemma and_left_true {a b : Prop} (Pa : a) : a ∧ b ↔ b :=
by rewrite [iff_true_intro Pa, true_and]

section def
variables {G S : Type} [group G] [fintype S]

definition is_fixed_point (hom : G → perm S) (H : finset G) (a : S) : Prop :=
∀ h, h ∈ H → hom h a = a

variables [decidable_eq S]

definition orbit (hom : G → perm S) (H : finset G) (a : S) : finset S :=
           image (move_by a) (image hom H)

definition fixed_points [reducible] (hom : G → perm S) (H : finset G) : finset S :=
{a ∈ univ | orbit hom H a = '{a}}

variable [decidable_eq G] -- required by {x ∈ H |p x} filtering

definition moverset (hom : G → perm S) (H : finset G) (a b : S) : finset G :=
           {f ∈ H | hom f a = b}

definition stab (hom : G → perm S) (H : finset G) (a : S) : finset G :=
           {f ∈ H | hom f a = a}

end def

section orbit_stabilizer

variables {G S : Type} [group G] [decidable_eq G] [fintype S] [decidable_eq S]

section

variables {hom : G → perm S} {H : finset G} {a : S} [Hom : is_hom_class hom]
include Hom

lemma exists_of_orbit {b : S} : b ∈ orbit hom H a → ∃ h, h ∈ H ∧ hom h a = b :=
      assume Pb,
      obtain p (Pp₁ : p ∈ image hom H) (Pp₂ : move_by a p = b), from exists_of_mem_image Pb,
      obtain h (Ph₁ : h ∈ H) (Ph₂ : hom h = p), from exists_of_mem_image Pp₁,
      have Phab : hom h a = b, from calc
        hom h a = p a : Ph₂
            ... = b   : Pp₂,
      exists.intro h (and.intro Ph₁ Phab)

lemma orbit_of_exists {b : S} : (∃ h, h ∈ H ∧ hom h a = b) → b ∈ orbit hom H a :=
assume Pex, obtain h PinH Phab, from Pex,
mem_image (mem_image_of_mem hom PinH) Phab

lemma is_fixed_point_of_mem_fixed_points :
  a ∈ fixed_points hom H → is_fixed_point hom H a :=
assume Pain, take h, assume Phin,
  eq_of_mem_singleton
    (of_mem_sep Pain ▸ orbit_of_exists (exists.intro h (and.intro Phin rfl)))

lemma mem_fixed_points_of_exists_of_is_fixed_point :
  (∃ h, h ∈ H) → is_fixed_point hom H a → a ∈ fixed_points hom H :=
assume Pex Pfp, mem_sep_of_mem !mem_univ
  (ext take x, iff.intro
    (assume Porb, obtain h Phin Pha, from exists_of_orbit Porb,
      by rewrite [mem_singleton_iff, -Pha, Pfp h Phin])
    (obtain h Phin, from Pex,
      by rewrite mem_singleton_iff;
         intro Peq; rewrite Peq;
         apply orbit_of_exists;
         existsi h; apply and.intro Phin (Pfp h Phin)))

lemma is_fixed_point_iff_mem_fixed_points_of_exists :
  (∃ h, h ∈ H) → (a ∈ fixed_points hom H ↔ is_fixed_point hom H a) :=
assume Pex, iff.intro is_fixed_point_of_mem_fixed_points (mem_fixed_points_of_exists_of_is_fixed_point Pex)

lemma is_fixed_point_iff_mem_fixed_points [finsubgH : is_finsubg H] :
  a ∈ fixed_points hom H ↔ is_fixed_point hom H a :=
is_fixed_point_iff_mem_fixed_points_of_exists (exists.intro 1 !finsubg_has_one)

lemma is_fixed_point_of_one : is_fixed_point hom ('{1}) a :=
take h, assume Ph, by rewrite [eq_of_mem_singleton Ph, hom_map_one]

lemma fixed_points_of_one : fixed_points hom ('{1}) = univ :=
ext take s, iff.intro (assume Pl, mem_univ s)
  (assume Pr, mem_fixed_points_of_exists_of_is_fixed_point
    (exists.intro 1 !mem_singleton) is_fixed_point_of_one)

open fintype
lemma card_fixed_points_of_one : card (fixed_points hom ('{1})) = card S :=
by rewrite [fixed_points_of_one]

end

-- these are already specified by stab hom H a
variables {hom : G → perm S} {H : finset G} {a : S}

variable [Hom : is_hom_class hom]
include Hom

lemma perm_f_mul (f g : G): perm.f ((hom f) * (hom g)) a = ((hom f) ∘ (hom g)) a :=
rfl

lemma stab_lmul {f g : G} : g ∈ stab hom H a → hom (f*g) a = hom f a :=
assume Pgstab,
have hom g a = a, from of_mem_sep Pgstab, calc
  hom (f*g) a = perm.f ((hom f) * (hom g)) a : is_hom hom
          ... = ((hom f) ∘ (hom g)) a        : by rewrite perm_f_mul
          ... = (hom f) a                    : by unfold comp; rewrite this

lemma stab_subset : stab hom H a ⊆ H :=
      begin
        apply subset_of_forall, intro f Pfstab, apply mem_of_mem_sep Pfstab
      end

lemma reverse_move {h g : G} : g ∈ moverset hom H a (hom h a) → hom (h⁻¹*g) a = a :=
assume Pg,
have hom g a = hom h a, from of_mem_sep Pg, calc
  hom (h⁻¹*g) a = perm.f ((hom h⁻¹) * (hom g)) a : by rewrite (is_hom hom)
  ... = ((hom h⁻¹) ∘ hom g) a                    : by rewrite perm_f_mul
  ... = perm.f ((hom h)⁻¹ * hom h) a             : by unfold comp; rewrite [this, perm_f_mul, hom_map_inv hom h]
  ... = perm.f (1 : perm S) a                    : by rewrite (mul.left_inv (hom h))
  ... = a                                        : by esimp

lemma moverset_inj_on_orbit : set.inj_on (moverset hom H a) (ts (orbit hom H a)) :=
      take b1 b2,
      assume Pb1, obtain h1 Ph1₁ Ph1₂, from exists_of_orbit Pb1,
      have Ph1b1 : h1 ∈ moverset hom H a b1,
        from mem_sep_of_mem Ph1₁ Ph1₂,
      assume Psetb2 Pmeq, begin
        subst b1,
        rewrite Pmeq at Ph1b1,
        apply of_mem_sep Ph1b1
      end

variable [finsubgH : is_finsubg H]
include finsubgH

lemma subg_stab_of_move {h g : G} :
      h ∈ H → g ∈ moverset hom H a (hom h a) → h⁻¹*g ∈ stab hom H a :=
      assume Ph Pg,
      have Phinvg : h⁻¹*g ∈ H, from begin
        apply finsubg_mul_closed H,
          apply finsubg_has_inv H, assumption,
          apply mem_of_mem_sep Pg
        end,
      mem_sep_of_mem Phinvg (reverse_move Pg)

lemma subg_stab_closed : finset_mul_closed_on (stab hom H a) :=
      take f g, assume Pfstab, have Pf : hom f a = a, from of_mem_sep Pfstab,
      assume Pgstab,
      have Pfg : hom (f*g) a = a, from calc
        hom (f*g) a = (hom f) a : stab_lmul Pgstab
        ... = a : Pf,
      have PfginH : (f*g) ∈ H,
        from finsubg_mul_closed H (mem_of_mem_sep Pfstab) (mem_of_mem_sep Pgstab),
      mem_sep_of_mem PfginH Pfg

lemma subg_stab_has_one : 1 ∈ stab hom H a :=
      have P : hom 1 a = a, from calc
        hom 1 a = perm.f (1 : perm S) a : {hom_map_one hom}
        ... = a                         : rfl,
      have PoneinH : 1 ∈ H, from finsubg_has_one H,
      mem_sep_of_mem PoneinH P

lemma subg_stab_has_inv : finset_has_inv (stab hom H a) :=
      take f, assume Pfstab, have Pf : hom f a = a, from of_mem_sep Pfstab,
      have Pfinv : hom f⁻¹ a = a, from calc
        hom f⁻¹ a = hom f⁻¹ ((hom f) a)      : by rewrite Pf
        ... = perm.f ((hom f⁻¹) * (hom f)) a : by rewrite perm_f_mul
        ... = hom (f⁻¹ * f) a                : by rewrite (is_hom hom)
        ... = hom 1 a                        : by rewrite mul.left_inv
        ... = perm.f (1 : perm S) a          : by rewrite (hom_map_one hom),
      have PfinvinH : f⁻¹ ∈ H, from finsubg_has_inv H (mem_of_mem_sep Pfstab),
      mem_sep_of_mem PfinvinH Pfinv

definition subg_stab_is_finsubg [instance] :
           is_finsubg (stab hom H a) :=
           is_finsubg.mk subg_stab_has_one subg_stab_closed subg_stab_has_inv

lemma subg_lcoset_eq_moverset {h : G} :
      h ∈ H → fin_lcoset (stab hom H a) h = moverset hom H a (hom h a) :=
      assume Ph, ext (take g, iff.intro
      (assume Pl, obtain f (Pf₁ : f ∈ stab hom H a) (Pf₂ : h*f = g), from exists_of_mem_image Pl,
       have Pfstab : hom f a = a, from of_mem_sep Pf₁,
       have PginH : g ∈ H, begin
        subst Pf₂,
        apply finsubg_mul_closed H,
          assumption,
          apply mem_of_mem_sep Pf₁
        end,
      have Pga : hom g a = hom h a, from calc
        hom g a = hom (h*f) a : by subst g
        ... = hom h a         : stab_lmul Pf₁,
      mem_sep_of_mem PginH Pga)
      (assume Pr, begin
       rewrite [↑fin_lcoset, mem_image_iff],
       existsi h⁻¹*g,
       split,
         exact subg_stab_of_move Ph Pr,
         apply mul_inv_cancel_left
       end))

lemma subg_moverset_of_orbit_is_lcoset_of_stab (b : S) :
      b ∈ orbit hom H a → ∃ h, h ∈ H ∧ fin_lcoset (stab hom H a) h = moverset hom H a b :=
      assume Porb,
      obtain p (Pp₁ : p ∈ image hom H) (Pp₂ : move_by a p = b), from exists_of_mem_image Porb,
      obtain h (Ph₁ : h ∈ H) (Ph₂ : hom h = p), from exists_of_mem_image Pp₁,
      have Phab : hom h a = b, from by subst p; assumption,
      exists.intro h (and.intro Ph₁ (Phab ▸ subg_lcoset_eq_moverset Ph₁))

lemma subg_lcoset_of_stab_is_moverset_of_orbit (h : G) :
      h ∈ H → ∃ b, b ∈ orbit hom H a ∧ moverset hom H a b = fin_lcoset (stab hom H a) h :=
      assume Ph,
      have Pha : (hom h a) ∈ orbit hom H a, by
        apply mem_image_of_mem; apply mem_image_of_mem; exact Ph,
      exists.intro (hom h a) (and.intro Pha (eq.symm (subg_lcoset_eq_moverset Ph)))

lemma subg_moversets_of_orbit_eq_stab_lcosets :
      image (moverset hom H a) (orbit hom H a) = fin_lcosets (stab hom H a) H :=
      ext (take s, iff.intro
      (assume Pl, obtain b Pb₁ Pb₂, from exists_of_mem_image Pl,
      obtain h Ph, from subg_moverset_of_orbit_is_lcoset_of_stab b Pb₁, begin
      rewrite [↑fin_lcosets, mem_image_eq],
      existsi h, subst Pb₂, assumption
      end)
      (assume Pr, obtain h Ph₁ Ph₂, from exists_of_mem_image Pr,
      obtain b Pb, from @subg_lcoset_of_stab_is_moverset_of_orbit G S _ _ _ _ hom H a Hom _ h Ph₁, begin
      rewrite [mem_image_eq],
      existsi b, subst Ph₂, assumption
      end))

open nat

theorem orbit_stabilizer_theorem : card H = card (orbit hom H a) * card (stab hom H a) :=
        calc card H = card (fin_lcosets (stab hom H a) H) * card (stab hom H a) : lagrange_theorem stab_subset
        ... = card (image (moverset hom H a) (orbit hom H a)) * card (stab hom H a) : subg_moversets_of_orbit_eq_stab_lcosets
        ... = card (orbit hom H a) * card (stab hom H a) : card_image_eq_of_inj_on moverset_inj_on_orbit

end orbit_stabilizer

section orbit_partition

variables {G S : Type} [group G] [decidable_eq G] [fintype S] [decidable_eq S]
variables {hom : G → perm S} [Hom : is_hom_class hom] {H : finset G} [subgH : is_finsubg H]
include Hom subgH

lemma in_orbit_refl {a : S} : a ∈ orbit hom H a :=
mem_image (mem_image (finsubg_has_one H) (hom_map_one hom)) rfl

lemma in_orbit_trans {a b c : S} :
  a ∈ orbit hom H b → b ∈ orbit hom H c → a ∈ orbit hom H c :=
assume Painb Pbinc,
obtain h PhinH Phba, from exists_of_orbit Painb,
obtain g PginH Pgcb, from exists_of_orbit Pbinc,
orbit_of_exists (exists.intro (h*g) (and.intro
  (finsubg_mul_closed H PhinH PginH)
  (calc hom (h*g) c = perm.f ((hom h) * (hom g)) c : is_hom hom
                ... = ((hom h) ∘ (hom g)) c        : by rewrite perm_f_mul
                ... = (hom h) b                    : Pgcb
                ... = a                            : Phba)))

lemma in_orbit_symm {a b : S} : a ∈ orbit hom H b → b ∈ orbit hom H a :=
assume Painb, obtain h PhinH Phba, from exists_of_orbit Painb,
have perm.f (hom h)⁻¹ a = b, by rewrite [-Phba, -perm_f_mul, mul.left_inv],
have (hom h⁻¹) a = b,        by rewrite [hom_map_inv, this],
orbit_of_exists (exists.intro h⁻¹ (and.intro (finsubg_has_inv H PhinH) this))

lemma orbit_is_partition : is_partition (orbit hom H) :=
take a b, propext (iff.intro
  (assume Painb, obtain h PhinH Phba, from exists_of_orbit Painb,
  ext take c, iff.intro
    (assume Pcina, in_orbit_trans Pcina Painb)
    (assume Pcinb, obtain g PginH Pgbc, from exists_of_orbit Pcinb,
      in_orbit_trans Pcinb (in_orbit_symm Painb)))
  (assume Peq, Peq ▸ in_orbit_refl))

variables (hom) (H)
open nat finset.partition fintype

definition orbit_partition : @partition S _ :=
mk univ (orbit hom H) orbit_is_partition
  (restriction_imp_union (orbit hom H) orbit_is_partition (λ a Pa, !subset_univ))

definition orbits : finset (finset S) := equiv_classes (orbit_partition hom H)

definition fixed_point_orbits : finset (finset S) :=
  {cls ∈ orbits hom H | card cls = 1}

variables {hom} {H}

lemma exists_iff_mem_orbits (orb : finset S) :
  orb ∈ orbits hom H ↔ ∃ a : S, orbit hom H a = orb :=
begin
  esimp [orbits, equiv_classes, orbit_partition],
  rewrite [mem_image_iff],
  apply iff.intro,
    intro Pl,
    cases Pl with a Pa,
    rewrite (and_left_true !mem_univ) at Pa,
    existsi a, exact Pa,
    intro Pr,
    cases Pr with a Pa,
    rewrite -true_and at Pa, rewrite -(iff_true_intro (mem_univ a)) at Pa,
    existsi a, exact Pa
end

lemma exists_of_mem_orbits {orb : finset S} :
  orb ∈ orbits hom H → ∃ a : S, orbit hom H a = orb :=
iff.elim_left (exists_iff_mem_orbits orb)

lemma fixed_point_orbits_eq : fixed_point_orbits hom H = image (orbit hom H) (fixed_points hom H) :=
ext take s, iff.intro
  (assume Pin,
   obtain Psin Ps, from iff.elim_left !mem_sep_iff Pin,
   obtain a Pa, from exists_of_mem_orbits Psin,
   mem_image
     (mem_sep_of_mem !mem_univ (eq.symm
       (eq_of_card_eq_of_subset (by rewrite [Pa, Ps])
         (subset_of_forall
           take x, assume Pxin, eq_of_mem_singleton Pxin ▸ in_orbit_refl))))
     Pa)
  (assume Pin,
   obtain a Pain Porba, from exists_of_mem_image Pin,
   mem_sep_of_mem
     (begin esimp [orbits, equiv_classes, orbit_partition], rewrite [mem_image_iff],
       existsi a, exact and.intro !mem_univ Porba end)
     (begin substvars, rewrite [of_mem_sep Pain] end))

lemma orbit_inj_on_fixed_points : set.inj_on (orbit hom H) (ts (fixed_points hom H)) :=
take a₁ a₂, begin
  rewrite [-*mem_eq_mem_to_set, ↑fixed_points, *mem_sep_iff],
  intro Pa₁ Pa₂,
  rewrite [and.right Pa₁, and.right Pa₂],
  exact eq_of_singleton_eq
end

lemma card_fixed_point_orbits_eq : card (fixed_point_orbits hom H) = card (fixed_points hom H) :=
by rewrite fixed_point_orbits_eq; apply card_image_eq_of_inj_on orbit_inj_on_fixed_points

lemma orbit_class_equation : card S = Sum (orbits hom H) card :=
class_equation (orbit_partition hom H)

lemma card_fixed_point_orbits : Sum (fixed_point_orbits hom H) card = card (fixed_point_orbits hom H) :=
calc Sum _ _ = Sum (fixed_point_orbits hom H) (λ x, 1) : Sum_ext (take c Pin, of_mem_sep Pin)
         ... = card (fixed_point_orbits hom H) * 1 : Sum_const_eq_card_mul
         ... = card (fixed_point_orbits hom H) : mul_one (card (fixed_point_orbits hom H))

local attribute nat.comm_semiring [instance]
lemma orbit_class_equation' : card S = card (fixed_points hom H) + Sum {cls ∈ orbits hom H | card cls ≠ 1} card :=
calc card S = Sum (orbits hom H) finset.card                                                            : orbit_class_equation
        ... = Sum (fixed_point_orbits hom H) finset.card + Sum {cls ∈ orbits hom H | card cls ≠ 1} card : Sum_binary_union
        ... = card (fixed_point_orbits hom H) + Sum {cls ∈ orbits hom H | card cls ≠ 1} card            : by rewrite -card_fixed_point_orbits
        ... = card (fixed_points hom H) + Sum {cls ∈ orbits hom H | card cls ≠ 1} card                  : by rewrite card_fixed_point_orbits_eq

end orbit_partition

section cayley
variables {G : Type} [group G] [fintype G]

definition action_by_lmul : G → perm G :=
take g, perm.mk (lmul_by g) (lmul_inj g)

variable [decidable_eq G]

lemma action_by_lmul_hom : homomorphic (@action_by_lmul G _ _) :=
take g₁ (g₂ : G), eq.symm (calc
      action_by_lmul g₁ * action_by_lmul g₂
    = perm.mk ((lmul_by g₁)∘(lmul_by g₂)) _ : rfl
... = perm.mk (lmul_by (g₁*g₂)) _ : by congruence; apply coset.lmul_compose)

lemma action_by_lmul_inj : injective (@action_by_lmul G _ _) :=
take g₁ g₂, assume Peq, perm.no_confusion Peq
  (λ Pfeq Pqeq,
  have Pappeq : g₁*1 = g₂*1, from congr_fun Pfeq _,
  calc g₁ = g₁ * 1 : mul_one
      ... = g₂ * 1 : Pappeq
      ... = g₂ : mul_one)

definition action_by_lmul_is_iso [instance] : is_iso_class (@action_by_lmul G _ _) :=
is_iso_class.mk action_by_lmul_hom action_by_lmul_inj

end cayley

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

definition ftfg [instance] : fintype (finset G) := sorry --shouldn't this be inferred by the typeclass mechanism?

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

section lcosets
open fintype subtype

variables {G : Type} [group G] [fintype G] [decidable_eq G]

variables H : finset G

definition action_on_lcoset : G → perm (lcoset_type univ H) :=
take g, perm.mk (lcoset_lmul (mem_univ g)) lcoset_lmul_inj

private definition lcoset_of (g : G) : lcoset_type univ H :=
tag (fin_lcoset H g) (exists.intro g (and.intro !mem_univ rfl))

variable {H}

lemma action_on_lcoset_eq (g : G) (J : lcoset_type univ H)
  : elt_of (action_on_lcoset H g J) = fin_lcoset (elt_of J) g := rfl

lemma action_on_lcoset_hom : homomorphic (action_on_lcoset H) :=
take g₁ g₂, eq_of_feq (funext take S, subtype.eq
  (by rewrite [↑action_on_lcoset, ↑lcoset_lmul, -fin_lcoset_compose]))

definition action_on_lcoset_is_hom [instance] : is_hom_class (action_on_lcoset H) :=
is_hom_class.mk action_on_lcoset_hom

variable [finsubgH : is_finsubg H]
include finsubgH

lemma aol_fixed_point_subset_normalizer (J : lcoset_type univ H) :
  is_fixed_point (action_on_lcoset H) H J → elt_of J ⊆ normalizer H :=
obtain j Pjin Pj, from exists_of_lcoset_type J,
assume Pfp,
have PH : ∀ {h}, h ∈ H → fin_lcoset (fin_lcoset H j) h = fin_lcoset H j,
  from take h, assume Ph, by rewrite [Pj, -action_on_lcoset_eq, Pfp h Ph],
subset_of_forall take g, begin
  rewrite [-Pj, fin_lcoset_same, -inv_inv at {2}],
  intro Pg,
  rewrite -Pg at PH,
  apply finsubg_has_inv,
  apply mem_sep_of_mem !mem_univ,
  intro h Ph,
  have Phg : fin_lcoset (fin_lcoset H g) h = fin_lcoset H g, from PH Ph,
  revert Phg,
  rewrite [↑conj_by, inv_inv, mul.assoc, fin_lcoset_compose, -fin_lcoset_same, ↑fin_lcoset, mem_image_iff, ↑lmul_by],
  intro Pex, cases Pex with k Pand, cases Pand with Pkin Pk,
  rewrite [-Pk, inv_mul_cancel_left], exact Pkin
end

lemma aol_fixed_point_of_mem_normalizer {g : G} :
  g ∈ normalizer H → is_fixed_point (action_on_lcoset H) H (lcoset_of H g) :=
assume Pgin, take h, assume Phin, subtype.eq
  (by rewrite [action_on_lcoset_eq, ↑lcoset_of, lrcoset_same_of_mem_normalizer Pgin, fin_lrcoset_comm, finsubg_lcoset_id Phin])

lemma aol_fixed_points_eq_normalizer :
  Union (fixed_points (action_on_lcoset H) H) elt_of = normalizer H :=
ext take g, begin
  rewrite [mem_Union_iff],
  apply iff.intro,
    intro Pl,
    cases Pl with L PL, revert PL,
    rewrite [is_fixed_point_iff_mem_fixed_points],
    intro Pg,
    apply mem_of_subset_of_mem,
      apply aol_fixed_point_subset_normalizer L, exact and.left Pg,
      exact and.right Pg,
    intro Pr,
    existsi (lcoset_of H g), apply and.intro,
      rewrite [is_fixed_point_iff_mem_fixed_points],
      exact aol_fixed_point_of_mem_normalizer Pr,
      exact fin_mem_lcoset g
end

open nat

lemma card_aol_fixed_points_eq_card_cosets :
  card (fixed_points (action_on_lcoset H) H) = card (lcoset_type (normalizer H) H) :=
have Peq : card (fixed_points (action_on_lcoset H) H) * card H = card (lcoset_type (normalizer H) H) * card H, from calc
  card _ * card H = card (Union (fixed_points (action_on_lcoset H) H) elt_of) : card_Union_lcosets
              ... = card (normalizer H) : aol_fixed_points_eq_normalizer
              ... = card (lcoset_type (normalizer H) H) * card H : lagrange_theorem' subset_normalizer,
eq_of_mul_eq_mul_right (card_pos_of_mem !finsubg_has_one) Peq

end lcosets

section perm_fin
open fin nat eq.ops

variable {n : nat}

definition lift_perm (p : perm (fin n)) : perm (fin (succ n)) :=
perm.mk (lift_fun p) (lift_fun_of_inj (perm.inj p))

definition lower_perm (p : perm (fin (succ n))) (P : p maxi = maxi) : perm (fin n) :=
perm.mk (lower_inj p (perm.inj p) P)
  (take i j, begin
  rewrite [-eq_iff_veq, *lower_inj_apply, eq_iff_veq],
  apply injective_comp (perm.inj p) lift_succ_inj
  end)

lemma lift_lower_eq : ∀ {p : perm (fin (succ n))} (P : p maxi = maxi),
  lift_perm (lower_perm p P) = p
| (perm.mk pf Pinj) := assume Pmax, begin
  rewrite [↑lift_perm], congruence,
  apply funext, intro i,
  have Pfmax : pf maxi = maxi, by apply Pmax,
  have Pd : decidable (i = maxi), from _,
    cases Pd with Pe Pne,
      rewrite [Pe, Pfmax], apply lift_fun_max,
      rewrite [lift_fun_of_ne_max Pne, ↑lower_perm, ↑lift_succ],
      rewrite [-eq_iff_veq, -val_lift, lower_inj_apply, eq_iff_veq],
      congruence, rewrite [-eq_iff_veq]
  end

lemma lift_perm_inj : injective (@lift_perm n) :=
take p1 p2, assume Peq, eq_of_feq (lift_fun_inj (feq_of_eq Peq))

lemma lift_perm_inj_on_univ : set.inj_on (@lift_perm n) (ts univ) :=
eq.symm to_set_univ ▸ iff.elim_left set.injective_iff_inj_on_univ lift_perm_inj

lemma lift_to_stab : image (@lift_perm n) univ = stab id univ maxi :=
ext (take (pp : perm (fin (succ n))), iff.intro
  (assume Pimg, obtain p P_ Pp, from exists_of_mem_image Pimg,
  have Ppp : pp maxi = maxi, from calc
    pp maxi = lift_perm p maxi : {eq.symm Pp}
        ... = lift_fun p maxi : rfl
        ... = maxi : lift_fun_max,
  mem_sep_of_mem !mem_univ Ppp)
  (assume Pstab,
  have Ppp : pp maxi = maxi, from of_mem_sep Pstab,
  mem_image !mem_univ (lift_lower_eq Ppp)))

definition move_from_max_to (i : fin (succ n)) : perm (fin (succ n)) :=
perm.mk (madd (i - maxi)) madd_inj

lemma orbit_max : orbit (@id (perm (fin (succ n)))) univ maxi = univ :=
ext (take i, iff.intro
  (assume P, !mem_univ)
  (assume P, begin
    apply mem_image,
      apply mem_image,
        apply mem_univ (move_from_max_to i), apply rfl,
      apply sub_add_cancel
    end))

lemma card_orbit_max : card (orbit (@id (perm (fin (succ n)))) univ maxi) = succ n :=
calc card (orbit (@id (perm (fin (succ n)))) univ maxi) = card univ : by rewrite orbit_max
                                                    ... = succ n    : card_fin (succ n)

open fintype

lemma card_lift_to_stab : card (stab (@id (perm (fin (succ n)))) univ maxi) = card (perm (fin n)) :=
 calc finset.card (stab (@id (perm (fin (succ n)))) univ maxi)
    = finset.card (image (@lift_perm n) univ) : by rewrite lift_to_stab
... = card univ                               : by rewrite (card_image_eq_of_inj_on lift_perm_inj_on_univ)

lemma card_perm_step : card (perm (fin (succ n))) = (succ n) * card (perm (fin n)) :=
 calc card (perm (fin (succ n)))
    = card (orbit id univ maxi) * card (stab id univ maxi) : orbit_stabilizer_theorem
... = (succ n) * card (stab id univ maxi)                  : {card_orbit_max}
... = (succ n) * card (perm (fin n))                       : by rewrite -card_lift_to_stab

end perm_fin
end group_theory
