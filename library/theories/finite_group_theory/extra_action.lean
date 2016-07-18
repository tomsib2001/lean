import algebra.group data theories.finite_group_theory.hom theories.finite_group_theory.perm theories.finite_group_theory.finsubg theories.finite_group_theory.action data.finset.extra_finset data.finset

-- namespace group_theory
open finset function perm group_theory nat

lemma eq_im_of_eq_f {A B : Type} [decidable_eq B] (f g : A → B) (S : finset A) : f = g → f ' S = g ' S := take Hfg, by rewrite Hfg


local attribute perm.f [coercion]

section action_on_subset

-- structure action_on [class]

end action_on_subset

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

-- set_option pp.implicit true
-- set_option pp.notation false

lemma conj_im_id (H : finset G) : conj_by 1 ' H = H :=
have conj_is_id : (conj_by : G → G → G) 1 = id, from funext (take x, by rewrite conj_id),
begin rewrite [conj_is_id],
rewrite image_id,
end

definition conj_subsets : G → group_theory.perm (finset G) :=
  λ (g : G), perm.mk (λ H, image (conj_by g) H)
  (take H1 H2 Heqg,
    have H : conj_by (g⁻¹) ' (conj_by g ' H1) = conj_by (g⁻¹) ' (conj_by g ' H2), from by rewrite Heqg,
    begin
     rewrite -image_comp at H,
     rewrite -image_comp at H,
     rewrite -conj_by_compose at H,
     rewrite (mul.left_inv g) at H,
     revert H,
     do 2 rewrite conj_im_id,
     simp
    end
  )

lemma perm_of_conj (g : G) : perm.f (conj_subsets g) = λ H, image (conj_by g) H := rfl

-- set_option pp.implicit true
-- set_option pp.notation false

local attribute perm.mul [reducible]

lemma conj_subsets_mult (g1 g2: G) : perm.mul (conj_subsets g1) (conj_subsets g2) = conj_subsets (g1 * g2) :=
begin
  apply eq_of_feq,
  rewrite perm_of_conj,
  rewrite ↑perm.mul,
  do 2 rewrite perm_of_conj,
  rewrite conj_by_image_compose
end

lemma homomorphic_conj_subsets : homomorphic (conj_subsets : G → group_theory.perm (finset G)) := take g1 g2,
have conj_subsets g1 * conj_subsets g2 = perm.mul (conj_subsets g1) (conj_subsets g2), from rfl,
begin
rewrite [this,conj_subsets_mult],
end

definition is_hom_conj_subsets [instance] : @is_hom_class G (perm (finset G)) _ _ conj_subsets := is_hom_class.mk homomorphic_conj_subsets

end action_by_conj

section partial_actions

open finset function

local attribute perm.f [coercion]

-- aT is the type of the acting group
-- rT is the return type of the set on which the action is done
variables {aT rT : Type} [group aT] [fintype rT] [fintype aT]
variables [Hdeceq_aT : decidable_eq aT]
variables [Hdeceq_rT : decidable_eq rT]
-- variable (D : finset aT) -- the domain


section defs


definition act_morph (D : finset aT) (to : rT → aT → rT) (x : rT) :=
  forall (a b : aT), a ∈ D → b ∈ D → to x (a * b) = to (to x a) b

definition left_injective {A B C : Type} (f : A → B → C) := forall (y: B), injective (λ x, f x y)

definition is_action [class] (D : finset aT) (to : rT → aT → rT) := left_injective to ∧ ∀ (x : rT),  act_morph D to x

-- definition act_dom D to := -- not sure how to define this one

set_option formatter.hide_full_terms false

include Hdeceq_aT

definition actm (D : finset aT) (to : rT → aT → rT) [Hact_to : is_action D to] a :=
  if a ∈ D then (λ x, to x a) else (id : rT → rT)

definition actm_inj (D : finset aT) (to : rT → aT → rT) [Hact_to : is_action D to] (a : aT) :
 injective (actm D to a) := take x y,
 begin cases decidable.em (a ∈ D) with aD naD,
 rewrite ↑actm,
 rewrite (if_pos aD),
 apply ((and.left Hact_to)),
 rewrite [↑actm,(if_neg naD),↑id],
 intro H, exact H
 end

definition actm_perm (D : finset aT) (to : rT → aT → rT) [Hact_to : is_action D to] (a : aT) : perm rT := perm.mk (actm D to a) (actm_inj D to a)

include Hdeceq_rT

-- the orbit of x under the action of A
definition orbit [reducible] (to : rT → aT → rT) (A : finset aT) (x : rT) := to x ' A

-- definition afix (to : rT → aT → rT) (A : finset aT) := { x ∈ univ | orbit to A x = '{x} }

definition afix [reducible] (to : rT → aT → rT) (A : finset aT) := { x ∈ univ | A ⊆ {a ∈ univ | to x a = x} }

-- definition is_fixed_point to A x :=

-- stabilizer in S : all elements a of the domain D such that the action of a fixes all S
-- Definition astab S to := D :&: [set a | S \subset [set x | to x a == x]].
definition astab [reducible] (D : finset aT) (S : finset rT) to := D ∩ { a ∈ univ | S ⊆ {x ∈ univ | to x a = x}}

-- (*      'N_A(S | to) == the global stabiliser of S : {set rT} in D :&: A.     *)
-- Definition astabs S to := D :&: [set a | S \subset to^~ a @^-1: S].
-- Notation "''N' ( S | to )" := (astabs S to)

definition astabs [reducible] (D : finset aT) S to := D ∩ { a ∈ univ | S ⊆ {(x : rT) ∈ univ | to x a ∈ S}}

-- Definition acts_on A S to := {in A, forall a x, (to x a \in S) = (x \in S)}.
-- this corresponds to  {acts A, on S | to} == A acts on the set S (Prop statement).
definition acts_on_prop [reducible] (A : finset aT) (S : finset rT) to := ∀ a s, a ∈ A → s ∈ S → (to s a ∈ S ↔ s ∈ S)

definition acts_on [reducible] (D : finset aT) (A : finset aT) (S : finset rT) to := A ⊆ astabs D S to

-- Definition atrans A S to := S \in orbit to A @: S.
definition atrans [reducible] (A : finset aT) (S : finset rT) to := S ∈ orbit to A ' S

definition faithful [reducible] (D : finset aT) (A : finset aT) (S : finset rT) to :=
A ∩ astab D S to

-- Notation "[ 'acts' A , 'on' S | to ]" := (A \subset pred_of_set 'N(S | to))


end defs

section rawaction
include Hdeceq_aT

variables (to : rT → aT → rT) (D : finset aT) [Hact_to : is_action D to]

lemma act_inj : left_injective to := and.left Hact_to

lemma actMin (x : rT) : act_morph D to x := and.right Hact_to x

include Hact_to

lemma actmEfun (a : aT) : a ∈ D -> actm D to a = λ x, to x a := take Ha, by rewrite [↑actm,(if_pos Ha)]

-- lemma act_morph_comp (a b : aT) : a ∈ D → b ∈ D → actm D to b ∘ actm D to a = actm D to (a * b) :=
-- take Ha Hb,
--   begin
--   rewrite (actmEfun to D a Ha),
--   rewrite (actmEfun to D b Hb),
--   apply funext, intro x,
--   rewrite ↑comp,
--   rewrite -(and.right Hact_to x a b Ha Hb),

-- end


-- omit Hact_to

include Hdeceq_rT
-- Lemma card_setact S a : #|to^* S a| = #|S|.
lemma card_setact S (a : aT) : card (actm D to a ' S) = card S :=
      begin
      apply card_image_eq_of_inj_on,
      intro x1 x2 Hx1S Hx2S,
      apply actm_inj
      end

-- Lemma setact_is_action : is_action D to^*.
lemma setact_is_action : is_action D (λ (S : finset rT) (a : aT) , (λ s, to s a) ' S) := and.intro (take y,
  begin
  apply injective_image,
  apply (and.left Hact_to),
  end)
  (take S, take a b Ha Hb,
  begin
  rewrite -image_comp,
  apply eq_im_of_eq_f,
  apply funext,
  intro x,
  rewrite [↑comp,-((and.right Hact_to) x a b Ha Hb)],
  end)

-- Lemma orbitP A x y :
--   reflect (exists2 a, a \in A & to x a = y) (y \in orbit to A x).
-- Proof. by apply: (iffP imsetP) => [] [a]; exists a. Qed.

lemma orbitP A (x y : rT) :
  y ∈ orbit to A x ↔ exists a, a ∈ A ∧ to x a = y :=
  iff.intro
  (take Hyorbit,
  begin
  rewrite ↑orbit at Hyorbit,
  rewrite mem_image_iff at Hyorbit,
  exact Hyorbit
  end)
  (take Him,
  begin
  rewrite [↑orbit,mem_image_iff],
  exact Him
  end)

lemma mem_orbit (A : finset aT) (x : rT) (a : aT) : a ∈ A → to x a ∈ orbit to A x := assume Ha, mem_image Ha rfl

lemma afixP (A : finset aT) (x : rT) : (∀ a, a ∈ A → to x a = x) ↔ x ∈ afix to A :=
begin
rewrite ↑afix,
apply iff.intro,
intro HA,
apply (mem_sep_of_mem (mem_univ x)),
apply subset_of_forall,
intro a Ha,
apply (mem_sep_of_mem (mem_univ a)),
apply HA,
exact Ha,
intro Hx,
rewrite mem_sep_iff at Hx,
cases Hx with Hxuniv HxA,
intro a Ha,
have Ha1 : a ∈ {a ∈ univ | to x a = x}, from mem_of_subset_of_mem HxA Ha,
rewrite mem_sep_iff at Ha1,
exact (and.right Ha1)
end

-- Lemma afixS A B : A \subset B -> 'Fix_to(B) \subset 'Fix_to(A).
lemma afixS (A B : finset aT) : A ⊆ B → afix to B ⊆ afix to A :=
  assume sAB,
  begin
  rewrite ↑afix,
  rewrite subset_sep_iff,
  intro x HBx,
  apply subset_of_forall,
  intro a Ha,
  apply mem_sep_of_mem (mem_univ _),
  apply (of_mem_sep (mem_of_subset_of_mem (subset.trans sAB HBx) Ha))
  end

-- Lemma afixU A B : 'Fix_to(A :|: B) = 'Fix_to(A) :&: 'Fix_to(B).
lemma afixU (A B : finset aT) : afix to (A ∩ B) = afix to A ∩ afix to B := sorry

-- Lemma afix1P a x : reflect (to x a = x) (x \in 'Fix_to[a]).
lemma afix1P (a : aT) (x : rT) : to x a = x ↔ x ∈ afix to '{a} :=
iff.intro  (assume Hxfix, mem_sep_of_mem (mem_univ _)
  (begin
  have ∀ b, b ∈ '{a} → b ∈ {a ∈ univ | to x a = x}, from take b Hb,
  begin
  apply mem_sep_of_mem (mem_univ _),
  rewrite mem_singleton_iff at Hb,
  rewrite Hb, exact Hxfix
  end,
  apply subset_of_forall this,
  end)) (take Hxfix,
  begin
  have H : '{a} ⊆ {a ∈ univ | to x a = x}, from of_mem_sep Hxfix,
  rewrite singleton_subset_iff at H,
  apply of_mem_sep H
  end)

-- Lemma astabIdom S : 'C_D(S | to) = 'C(S | to).
lemma astabIdom (S : finset rT) : D ∩ astab D S to = astab D S to :=
  begin
    rewrite ↑astab,
    rewrite -inter_assoc,
    rewrite inter_self,
  end

-- Lemma astab_dom S : {subset 'C(S | to) <= D}.
lemma astab_dom (S : finset rT) : astab D S to ⊆ D := finset_inter_subset_left

-- Lemma astab_act S a x : a \in 'C(S | to) -> x \in S -> to x a = x.
lemma astab_act (S : finset rT) (a : aT) (x : rT) : a ∈ astab D S to → x ∈ S → to x a = x :=
  begin
    intro Ha Hx,
    rewrite mem_inter_iff at Ha,
    cases Ha with HaD Hasep,
    have HSx : S ⊆ {x ∈ univ | to x a = x}, from of_mem_sep Hasep,
    apply of_mem_sep (mem_of_subset_of_mem HSx Hx),
  end

-- Lemma astabS S1 S2 : S1 \subset S2 -> 'C(S2 | to) \subset 'C(S1 | to).
lemma astabS (S1 S2 : finset rT) : S1 ⊆ S2 → astab D S2 to ⊆  astab D S1 to :=
  assume s12,
  subset_of_forall
  (take a Ha,
  mem_inter
  (mem_of_subset_of_mem (astab_dom to D S2) Ha)
   (mem_sep_of_mem !mem_univ (subset_of_forall (take x HxS1, (mem_sep_of_mem !mem_univ (astab_act to D S2 a x Ha (mem_of_subset_of_mem s12 HxS1)))))))

-- Lemma astabsIdom S : 'N_D(S | to) = 'N(S | to).
lemma astabsIdom (S : finset rT) : D ∩ astabs D S to ⊆ astabs D S to :=
  finset_inter_subset_right

-- Lemma astabs_dom S : {subset 'N(S | to) <= D}.
lemma astabs_dom (S : finset rT) : astabs D S to ⊆ D :=
  finset_inter_subset_left

-- Lemma astabs_act S a x : a \in 'N(S | to) -> (to x a \in S) = (x \in S).
lemma astabs_act (S : finset rT) (a : aT) (x : rT) : a ∈ astabs D S to → (to x a ∈ S ↔ x ∈ S) :=
  assume Ha,
  begin
  rewrite ↑astabs at Ha,
  rewrite mem_inter_iff at Ha,
  cases Ha with HaD HS,
  have HS1 : S ⊆ { x ∈ univ | to x a ∈ S}, from of_mem_sep HS,
  have hsImS : image (λ x, to x a) { x ∈ univ | to x a ∈ S} ⊆ S, from
  subset_of_forall
  (take x Hx,
  begin
  rewrite mem_image_iff at Hx,
  cases Hx with x1 Hx1,
  cases Hx1 with Hx1 Hx1ax,
  rewrite -Hx1ax, apply of_mem_sep Hx1
  end),
  have HeqCard1 : card (image (λ x, to x a) { x ∈ univ | to x a ∈ S}) = card { x ∈ univ | to x a ∈ S}, from
  card_image_eq_of_inj_on (take u v Hu Hv, begin apply act_inj to D a end),
  have card (image (λ x, to x a) { x ∈ univ | to x a ∈ S}) ≤ card S, from
  card_le_card_of_subset hsImS,
  have HleCard1 : card { x ∈ univ | to x a ∈ S} ≤ card S, from
  eq.subst HeqCard1 this,
  have HleCard2 : card { x ∈ univ | to x a ∈ S} ≥ card S, from
  card_le_card_of_subset HS1,
  have card { x ∈ univ | to x a ∈ S} = card S, from eq_of_le_of_ge HleCard1 HleCard2,
  have HeqStoS : S = { x ∈ univ | to x a ∈ S}, from sorry, -- there should be a lemma to deduce this, this is easy!! TODO
  apply iff.intro,
  intro HxaS,
  rewrite HeqStoS,
  apply (mem_sep_of_mem !mem_univ),
  exact HxaS,
  intro HxS, apply of_mem_sep (eq.subst HeqStoS HxS),
  end

-- Lemma astab_sub S : 'C(S | to) \subset 'N(S | to).
lemma astab_sub (S : finset rT) : astab D S to ⊆ astabs D S to :=
  subset_of_forall (take a Ha,
  mem_inter (mem_of_subset_of_mem (astab_dom to D S) Ha) (mem_sep_of_mem !mem_univ
  begin
   apply subset_of_forall,
   intro x HxS,
   apply mem_sep_of_mem,
   apply !mem_univ,
   rewrite (astab_act to D S a x Ha HxS),
   exact HxS
  end
  ))

-- Lemma astabsC S : 'N(~: S | to) = 'N(S | to).

-- Lemma astabsI S T : 'N(S | to) :&: 'N(T | to) \subset 'N(S :&: T | to).

-- Lemma astabs_setact S a : a \in 'N(S | to) -> to^* S a = S.

-- Lemma astab1_set S : 'C[S | set_action] = 'N(S | to).

-- Lemma astabs_set1 x : 'N([set x] | to) = 'C[x | to].

-- Lemma acts_dom A S : [acts A, on S | to] -> A \subset D.

lemma acts_dom (A : finset aT) (S : finset rT) : acts_on D A S to → A ⊆ D :=
  take Hacts, subset.trans Hacts !finset_inter_subset_left


-- Lemma acts_act A S : [acts A, on S | to] -> {acts A, on S | to}.

lemma acts_act (A : finset aT) (S : finset rT) : acts_on D A S to → acts_on_prop A S to :=
  assume Hacts_on,
  begin intros a x Ha Hx,
  have a ∈ astabs D S to ,
  from mem_of_subset_of_mem Hacts_on Ha,
  exact (astabs_act to D S a x this)
  end

-- mem_inter (mem_of_subset_of_mem (astab_dom to D S) Ha) (mem_sep_of_mem !mem_univ
--   begin
--   have _, from astabs_act
--   end))

end rawaction

section partial_action

variables (to : rT → aT → rT) (D : finset aT) [Hact_to : is_action D to]
variable [HsubgD : is_finsubg D]
include Hdeceq_rT
include HsubgD Hact_to

lemma act1 (x : rT) : to x 1 = x :=
  begin
  apply (act_inj to D 1),
  have 1 ∈ D, from finsubg_has_one D,
  rewrite -(actMin to D x 1 1 this this),
  rewrite one_mul,
  end

lemma actKin (x : rT) (a : aT) : a ∈ D →  to (to x a) a⁻¹ = x :=
  assume HaD,
  begin
  rewrite -(actMin to D x a a⁻¹ HaD (finsubg_has_inv D HaD)),
  have a * a⁻¹ = 1, from sorry, -- can't find this!!!!
  rewrite this,
  apply (act1 to D x)
  end

lemma actKVin (x : rT) (a : aT) : a ∈ D → to (to x a⁻¹) a = x :=
  assume HaD,
  begin
    rewrite -(inv_inv a) at {2},
    rewrite (actKin to D x (a⁻¹) (finsubg_has_inv D HaD)),
  end

lemma orbit_refl G [is_finsubg G] (x : rT) : x ∈ orbit to G x :=
  begin
  -- rewrite -(act1 to D),
  have to x 1 ∈ orbit to G x, from (mem_orbit to D G x 1 (finsubg_has_one G)),
  exact (eq.subst (act1 to D x) this)
  end

-- Lemma orbit_in_sym G : G \subset D -> symmetric (orbit_rel G).

definition orbit_rel A := λ x y, x ∈ orbit to A y



lemma orbit_in_sym (G : finset aT) [is_finsubg G] : G ⊆ D → symmetric (orbit_rel to D G) := assume sGD, take x y, assume Hxy,
  begin
  rewrite ↑orbit_rel at Hxy,
  rewrite (orbitP to D) at Hxy,
  rewrite [↑orbit_rel,orbitP to D],
  cases Hxy with g Hg,
  cases Hg with HgG Hgyx,
  apply (exists.intro g⁻¹),
  apply and.intro,
  apply (finsubg_has_inv G HgG),
  rewrite -Hgyx,
  rewrite (actKin to D y g (mem_of_subset_of_mem sGD HgG))
  end



-- Lemma orbit_in_trans G : G \subset D -> transitive (orbit_rel G).

lemma orbit_in_trans (G : finset aT) [is_finsubg G]: G ⊆ D → transitive (orbit_rel to D G) := assume sGD,
  begin
    intro x y z Hxy Hyz,
    rewrite ↑orbit_rel at Hxy,
    rewrite ↑orbit_rel at Hyz,
    rewrite (orbitP to D) at Hxy,
    rewrite (orbitP to D) at Hyz,
    cases Hxy with g Hg,
    cases Hg with HgG Hgyx,
    cases Hyz with g1 Hg1,
    cases Hg1 with Hg1G Hg1yz,
    rewrite [↑orbit_rel,orbitP to D],
    apply (exists.intro (g1 * g)),
    apply and.intro,
    apply (finsubg_mul_closed _ Hg1G HgG),
    rewrite [-Hgyx,-Hg1yz],
    rewrite (actMin to D z g1 g (mem_of_subset_of_mem sGD Hg1G) (mem_of_subset_of_mem sGD HgG)),
  end

-- Lemma orbit_in_eqP G x y :
--  G \subset D -> reflect (orbit to G x = orbit to G y) (x \in orbit to G y).
lemma orbit_in_eqP (G : finset aT) [is_finsubg G] (x y : rT) :
  G ⊆ D →
  ((orbit to G x = orbit to G y) ↔ (x ∈ orbit to G y)) :=
  begin
  intro sGD,
  apply iff.intro,
  intro Heq, rewrite -Heq, apply (orbit_refl to D),
  intro Hxorby,
  apply ext,
  intro a,
  apply iff.intro,
  intro Hax,
  apply (orbit_in_trans to D G sGD Hax Hxorby),
  intro Hay,
  apply (orbit_in_sym to D G sGD),
  apply (orbit_in_trans to D G sGD),
  apply Hxorby,
  apply (orbit_in_sym to D G sGD),
  apply Hay
  end

-- this is the wrong kind of partition, on the whole type
lemma orbit_partition (G : finset aT) [is_finsubg G] (S : finset rT) :
  acts_on D G S to → is_partition (orbit to D) :=
  assume Hacts_on,
  have sGD : G ⊆ D, from acts_dom to D G S Hacts_on,
  begin
    intro a b,
    apply classical.eq.of_iff,
    apply iff.intro,
    rewrite (orbit_in_eqP to D D a b !subset.refl),
    intro H, exact H,
    intro H,
    rewrite -(orbit_in_eqP to D D a b !subset.refl),
    exact H
  end


end partial_action

end partial_actions
