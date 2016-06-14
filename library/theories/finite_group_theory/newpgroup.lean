import data algebra.group .subgroup .finsubg theories.number_theory.pinat .cyclic

open nat finset fintype group_theory

-- useful for debugging
set_option formatter.hide_full_terms false

definition pred_p [reducible] (p : nat) : nat → Prop := λ n, n = p

section set_missing

lemma image_singleton {A B : Type} [hA: decidable_eq A] [hB: decidable_eq B] (f : A → B) (a : A) : image f (insert a empty) =  insert (f a) empty :=
begin
rewrite image_insert
end


lemma insert_empty {A : Type} [hAdec : decidable_eq A] (a : A) (b : A) : finset.insert a finset.empty = insert b empty → a = b :=
assume Heq_set,
have Hab : mem a (insert b empty), from (eq.subst Heq_set (mem_insert a empty)),
or.elim (eq.subst (mem_insert_eq a b empty) Hab) (take H, H)
begin
intro Habs,
exact false.elim (not_mem_empty a Habs)
end

end set_missing

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
  apply sorry
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

definition is_finsubg_prop [reducible] (A : finset G) : Prop :=
  1 ∈ A ∧ finset_mul_closed_on A ∧ finset_has_inv A


lemma is_finsub_is_finsubg_prop {A : finset G} : is_finsubg_prop A → is_finsubg A :=
  assume H,
  is_finsubg.mk (and.left H) (and.left (and.right H)) (and.right (and.right H))

lemma decidable_is_finsubg_prop [instance] {A : finset G} : decidable (is_finsubg_prop A) := _

reveal decidable_is_finsubg_prop

end groups_missing


definition pgroup [reducible] (pi : ℕ → Prop) (H : finset G) := is_pi_nat pi (card H)

lemma pgroup_dec (pi : ℕ → Prop) [Hdecpi : ∀ p, decidable (pi p)] (H : finset G) :
decidable (pgroup pi H) := _

definition p_subgroup (pi : ℕ → Prop) (H1 H2 : finset G) := subset H1 H2 ∧ pgroup pi H1

definition p_elt (pi : ℕ → Prop) (x : G) : Prop := is_pi_nat pi (order x)

-- the index of the subgroup A inside the group B
definition index [reducible] (A B : finset G) -- (Psub : finset.subset A B)
:= finset.card (fin_lcosets A B)

definition Hall [reducible] (A B : finset G) :=
subset A B ∧ coprime (card A) (index A B)

definition pHall [reducible] (pi : ℕ → Prop) [Hdecpi : ∀ p, decidable (pi p)] (A B : finset G) :=
subset A B ∧ pgroup pi A ∧ is_pi'_nat pi (index A B)

-- the set of p-Sylows of a subset A
definition Syl (p : nat) (A : finset G) :=
{ S ∈ finset.powerset A | is_finsubg_prop S ∧ pHall (pred_p p) S A }

-- Definition Sylow A B := p_group B && Hall A B.
definition is_sylow p (A B : finset G) := pgroup (pred_p p) A ∧ Hall A B

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
  ...              = finset.card B : sorry -- (card_eq_card_image_of_inj (inj_fin_lcoset_one))
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
