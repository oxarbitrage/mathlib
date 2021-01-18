import algebra.big_operators.finsupp
import algebra.floor
import analysis.special_functions.pow
import combinatorics.pigeonhole
import group_theory.quotient_group
import linear_algebra.determinant
import linear_algebra.free_module
import linear_algebra.matrix
import ring_theory.class_group
import ring_theory.dedekind_domain
import ring_theory.fractional_ideal

-- These results are in separate files for faster re-compiling.
-- They should be merged with the appropriate lower-level file when development is finished.
import algebraic_number_theory.class_number.det
import algebraic_number_theory.class_number.euclidean_absolute_value
import algebraic_number_theory.class_number.integral_closure

open ring

open_locale big_operators

section euclidean_domain

variables {R K L : Type*} [euclidean_domain R] [field K] [field L]
variables (f : fraction_map R K)
variables [algebra f.codomain L] [finite_dimensional f.codomain L] [is_separable f.codomain L]
variables [algebra R L] [is_scalar_tower R f.codomain L]
variables [decidable_eq L]

variables (L)

lemma integral_closure.dim_pos : 0 < integral_closure.dim L f :=
sorry

/-- If `a : integral_closure R L` has coordinates `≤ y`, `norm a ≤ norm_bound L f abs * y ^ n`. -/
noncomputable def norm_bound (abs : absolute_value R ℤ) : ℤ :=
let n := integral_closure.dim L f,
    h : 0 < integral_closure.dim L f := integral_closure.dim_pos L f,
    m : ℤ := finset.max' (finset.univ.image (λ (ijk : fin _ × fin _ × fin _),
        abs (matrix.lmul (integral_closure.is_basis L f) (integral_closure.basis L f ijk.1) ijk.2.1 ijk.2.2)))
        ⟨_, finset.mem_image.mpr ⟨⟨⟨0, h⟩, ⟨0, h⟩, ⟨0, h⟩⟩, finset.mem_univ _, rfl⟩⟩
in nat.factorial n • (n • m) ^ n

lemma norm_bound_pos (abs : absolute_value R ℤ) : 0 < norm_bound L f abs :=
begin
  obtain ⟨i, j, k, hijk⟩ : ∃ i j k,
    matrix.lmul (integral_closure.is_basis L f) (integral_closure.basis L f i) j k ≠ 0,
  { by_contra h,
    push_neg at h,
    apply (integral_closure.is_basis L f).ne_zero ⟨0, integral_closure.dim_pos L f⟩,
    apply (matrix.lmul _).injective_iff.mp (matrix.lmul_injective (integral_closure.is_basis L f)),
    ext j k,
    rw [h, matrix.zero_apply] },
  simp only [norm_bound, algebra.smul_def, ring_hom.eq_nat_cast, int.nat_cast_eq_coe_nat],
  apply mul_pos (int.coe_nat_pos.mpr (nat.factorial_pos _)),
  apply pow_pos (mul_pos (int.coe_nat_pos.mpr (integral_closure.dim_pos L f)) _),
  apply lt_of_lt_of_le (abs.pos hijk) (finset.le_max' _ _ _),
  exact finset.mem_image.mpr ⟨⟨i, j, k⟩, finset.mem_univ _, rfl⟩
end

lemma norm_le (a : integral_closure R L) {abs : absolute_value R ℤ}
  {y : ℤ} (hy : ∀ k, abs ((integral_closure.is_basis L f).repr a k) ≤ y) :
  abs_norm f abs a ≤ norm_bound L f abs * y ^ (integral_closure.dim L f) :=
begin
  conv_lhs { rw ← sum_repr (integral_closure.is_basis L f) a },
  unfold abs_norm algebra.norm norm_bound,
  rw [monoid_hom.coe_mk, matrix.to_matrix_lmul_eq],
  simp only [alg_hom.map_sum, alg_hom.map_smul],
  convert det_sum_le finset.univ _ hy;
    try { simp only [finset.card_univ, fintype.card_fin] },
  { rw [algebra.smul_mul_assoc, ← mul_pow _ _ (integral_closure.dim L f)],
    conv_lhs { rw algebra.smul_mul_assoc } },
  { intros i j k,
    apply finset.le_max',
    exact finset.mem_image.mpr ⟨⟨i, j, k⟩, finset.mem_univ _, rfl⟩ },
end

lemma finset.map_max' {α β : Type*} [linear_order α] [linear_order β]
  {f : α → β} (hf : monotone f) (s : finset α) (h : s.nonempty) :
  f (s.max' h) = (s.image f).max' (h.image f) :=
begin
  obtain mem := finset.max'_mem s h,
  refine le_antisymm
    (finset.le_max' _ _ (finset.mem_image.mpr ⟨_, mem, rfl⟩))
    (finset.max'_le _ _ _ (λ y hy, _)),
  obtain ⟨x, hx, rfl⟩ := finset.mem_image.mp hy,
  exact hf (finset.le_max' _ _ hx)
end

lemma finset.max'_lt {α : Type*} [linear_order α] (s : finset α) (h : s.nonempty)
  {x : α} (hx : ∀ y ∈ s, y < x) :
  s.max' h < x :=
lt_of_le_of_ne
  (finset.max'_le _ h _ (λ y hy, le_of_lt (hx y hy)))
  (ne_of_lt (hx _ (s.max'_mem h)))

lemma norm_lt {S : Type*} [linear_ordered_comm_ring S]
  (a : integral_closure R L) {abs : absolute_value R ℤ}
  {y : S} (hy : ∀ k, (abs ((integral_closure.is_basis L f).repr a k) : S) < y) :
  (abs_norm f abs a : S) < norm_bound L f abs * y ^ (integral_closure.dim L f) :=
begin
  have h : 0 < integral_closure.dim L f := integral_closure.dim_pos L f,
  have him : (finset.univ.image (λ k, abs ((integral_closure.is_basis L f).repr a k))).nonempty :=
    ⟨_, finset.mem_image.mpr ⟨⟨0, h⟩, finset.mem_univ _, rfl⟩⟩,
  set y' : ℤ := finset.max' _ him with y'_def,
  have hy' : ∀ k, abs ((integral_closure.is_basis L f).repr a k) ≤ y',
  { intro k,
    exact finset.le_max' _ _ (finset.mem_image.mpr ⟨k, finset.mem_univ _, rfl⟩) },
  have : (y' : S) < y,
  { rw [y'_def, finset.map_max' (show monotone (coe : ℤ → S), from λ x y h, int.cast_le.mpr h)],
    apply finset.max'_lt _ (him.image _),
    simp only [finset.mem_image, exists_prop],
    rintros _ ⟨x, ⟨k, -, rfl⟩, rfl⟩,
    exact hy k },
  have y'_nonneg : 0 ≤ y' := le_trans (abs.nonneg _) (hy' ⟨0, h⟩),
  apply lt_of_le_of_lt (int.cast_le.mpr (norm_le L f a hy')),
  simp only [int.cast_mul, int.cast_pow],
  apply mul_lt_mul' (le_refl _),
  { exact pow_lt_pow_of_lt_left this (int.cast_nonneg.mpr y'_nonneg) h },
  { exact pow_nonneg (int.cast_nonneg.mpr y'_nonneg) _ },
  { exact int.cast_pos.mpr (norm_bound_pos L f abs) },
  { apply_instance }
end

section admissible

/-- TODO: is this the right abstraction? -/
structure admissible_absolute_value (R : Type*) [euclidean_domain R]
  extends euclidean_absolute_value R ℤ :=
(card : ℝ → ℕ)
(exists_approx' : ∀ (ε : ℝ) (hε : 0 < ε) (b : R) (A : fin (card ε).succ → R),
  ∃ i₀ i₁, (i₀ ≠ i₁) ∧ (to_fun (A i₁ % b - A i₀ % b) : ℝ) < to_fun b • ε)

variables (abs : admissible_absolute_value R)

namespace admissible_absolute_value

instance : has_coe_to_fun (admissible_absolute_value R) :=
{ F := _,
  coe := λ abs, abs.to_fun }

instance : has_coe (admissible_absolute_value R) (euclidean_absolute_value R ℤ) :=
⟨λ abs, abs.to_euclidean_absolute_value⟩

instance : has_coe (admissible_absolute_value R) (absolute_value R ℤ) :=
⟨λ abs, abs.to_euclidean_absolute_value.to_absolute_value⟩

lemma nonneg (x : R) : 0 ≤ abs x := abs.to_euclidean_absolute_value.nonneg x

@[simp]
lemma eq_zero_iff {x : R} : abs x = 0 ↔ x = 0 :=
abs.to_euclidean_absolute_value.map_eq_zero_iff' x

@[simp]
lemma map_zero : abs 0 = 0 :=
abs.to_euclidean_absolute_value.map_zero

lemma map_ne_zero {x : R} : abs x ≠ 0 ↔ x ≠ 0 :=
abs.to_euclidean_absolute_value.map_ne_zero

/-- `simp`-normal form version of `f.map_ne_zero` -/
@[simp]
lemma map_ne_zero' {x : R} : ¬ (abs x = 0) ↔ ¬ (x = 0) :=
abs.to_euclidean_absolute_value.map_ne_zero'

lemma pos {x : R} (hx : x ≠ 0) : 0 < abs x :=
abs.to_euclidean_absolute_value.pos hx

@[simp]
lemma map_mul (x y : R) : abs (x * y) = abs x * abs y :=
abs.to_euclidean_absolute_value.map_mul x y

lemma le_add (x y : R) : abs (x + y) ≤ abs x + abs y :=
abs.to_euclidean_absolute_value.le_add x y

@[simp]
lemma map_lt_map_iff {x y : R} : abs x < abs y ↔ euclidean_domain.r x y :=
abs.to_euclidean_absolute_value.map_lt_map_iff

lemma mod_lt (a : R) {b : R} (hb : b ≠ 0) :
  abs (a % b) < abs b :=
abs.to_euclidean_absolute_value.sub_mod_lt a hb

@[simp]
lemma map_sub_eq_zero_iff (a b : R) :
  abs (a - b) = 0 ↔ a = b :=
abs.to_euclidean_absolute_value.map_sub_eq_zero_iff a b

lemma exists_approx {ε : ℝ} (hε : 0 < ε) (b : R) (A : fin (abs.card ε).succ → R) :
  ∃ i₀ i₁, i₀ ≠ i₁ ∧ (abs (A i₁ % b - A i₀ % b) : ℝ) < abs b • ε :=
abs.exists_approx' _ hε b A

lemma finset.exists_eq_insert_of_lt_card {α : Type*} [decidable_eq α] (n : ℕ) (s : finset α)
  (h : n < s.card) : ∃ (x : α) (t : finset α), s = insert x t ∧ n ≤ t.card :=
begin
  have : 0 < s.card := by linarith,
  obtain ⟨x, hx⟩ := finset.card_pos.mp this,
  use [x, s.erase x, (finset.insert_erase hx).symm],
  rw finset.card_erase_of_mem hx,
  exact nat.le_pred_of_lt h
end

lemma finset.card_le_one_of_subsingleton {α : Type*} [subsingleton α]
  (s : finset α) : s.card ≤ 1 :=
finset.card_le_one_iff.mpr (λ x y _ _, subsingleton.elim x y)

noncomputable def finset.to_vec {α : Type*} [decidable_eq α] :
  ∀ (s : finset α) {n : ℕ} (hn : n ≤ finset.card s), fin n → α
| s 0       hn i := fin_zero_elim i
| s (n + 1) hn i := let h : ∃ x, x ∈ s := finset.card_pos.mp (by linarith)
in @fin.cons _ (λ _, α) (classical.some h) ((s.erase (classical.some h)).to_vec
  (by { rw finset.card_erase_of_mem (show classical.some h ∈ s, from classical.some_spec h),
        exact nat.le_pred_of_lt hn })) i

lemma finset.to_vec_injective {α : Type*} [decidable_eq α] :
  ∀ (s : finset α) {n : ℕ} (hn : n ≤ finset.card s),
  function.injective (finset.to_vec s hn) := sorry

lemma finset.to_vec_mem {α : Type*} [decidable_eq α] :
  ∀ (s : finset α) {n : ℕ} (hn : n ≤ finset.card s) (i : fin n),
  finset.to_vec s hn i ∈ s
| s 0       hn i := fin_zero_elim i
| s (n + 1) hn i :=
let h : ∃ x, x ∈ s := finset.card_pos.mp (by linarith)
in fin.cases (show classical.some h ∈ s, from classical.some_spec h) sorry i

/-- We can partition a finite family into `M` sets, such that the remainders
in each set are close together. -/
lemma exists_partition (n : ℕ) {ε : ℝ} (hε : 0 < ε) (b : R) (A : fin n → R) :
  ∃ (t : fin n → fin (abs.card ε)),
    ∀ i₀ i₁, t i₀ = t i₁ → (abs (A i₁ % b - A i₀ % b) : ℝ) < abs b • ε :=
begin
  induction n with n ih,
  { sorry },
  obtain ⟨t', ht'⟩ := ih (fin.tail A),
  sorry,
end

lemma exists_approx_vec (n : ℕ) :
  ∀ {ε : ℝ} (hε : 0 < ε) {b : R} (hb : b ≠ 0) (A : fin (abs.card ε ^ n).succ → (fin n → R)),
  ∃ (i₀ i₁), (i₀ ≠ i₁) ∧ ∀ k, (abs (A i₁ k % b - A i₀ k % b) : ℝ) < abs b • ε :=
begin
  haveI := classical.dec_eq R,
  induction n with n ih,
  { intros ε hε b hb A,
    refine ⟨0, 1, _, _⟩,
    { simp },
    rintros ⟨i, ⟨⟩⟩ },
  intros ε hε b hb A,
  by_cases hA : ∃ i₀ i₁, i₀ ≠ i₁ ∧ A i₀ = A i₁,
  { obtain ⟨i₀, i₁, h, eq⟩ := hA,
    refine ⟨i₀, i₁, h, λ k, _⟩,
    rw [eq, sub_self, abs.map_zero, algebra.smul_def, int.cast_zero, ring_hom.eq_int_cast],
    exact mul_pos (int.cast_pos.mpr (abs.pos hb)) hε },
  have A_inj : function.injective A,
  { simp only [not_exists, not_and, ne.def, not_imp_not] at hA,
    exact λ x y h, hA x y h },
  set M := abs.card ε with hM,
  -- By the "nicer" pigeonhole principle, we can find a collection `s`
  -- of more than `M^n` elements where the first components lie close together:
  obtain ⟨s, s_inj, hs⟩ : ∃ s : fin (M ^ n).succ → fin (M ^ n.succ).succ,
    function.injective s ∧
    ∀ i₀ i₁, (abs (A (s i₁) 0 % b - A (s i₀) 0 % b) : ℝ) < abs b • ε,
  { -- We can partition the `A`s into `m` subsets where
    -- the first components lie close together:
    obtain ⟨t, ht⟩ : ∃ (t : fin (M ^ n.succ).succ → fin M),
      ∀ i₀ i₁, t i₀ = t i₁ → (abs (A i₁ 0 % b - A i₀ 0 % b) : ℝ) < abs b • ε :=
      abs.exists_partition _ hε b (λ x, A x 0),
    -- Since the `M` subsets contain more than `M * M^n` elements total,
    -- there must be a subset that contains more than `M^n` elements.
    obtain ⟨s, hs⟩ := @fintype.exists_lt_card_fiber_of_mul_lt_card _ _ _ _ _ t (M ^ n)
      (by simpa only [fintype.card_fin, pow_succ] using nat.lt_succ_self (M ^ n.succ) ),
    refine ⟨finset.to_vec _ hs, finset.to_vec_injective _ hs, λ i₀ i₁, ht _ _ _⟩,
    have := finset.to_vec_mem (finset.univ.filter (λ x, t x = s)) hs,
    obtain ⟨_, h₀⟩ := finset.mem_filter.mp (this i₀),
    obtain ⟨_, h₁⟩ := finset.mem_filter.mp (this i₁),
    exact h₀.trans h₁.symm },
  -- Since `s` is large enough, there are two elements of `A ∘ s`
  -- where the second components lie close together.
  obtain ⟨k₀, k₁, hk, h⟩ := ih hε hb (λ x, fin.tail (A (s x))),
  refine ⟨s k₀, s k₁, λ h, hk (s_inj h), λ i, fin.cases _ (λ i, _) i⟩,
  { exact hs k₀ k₁ },
  { exact h i },
end

end admissible_absolute_value

end admissible

section

variables (L)
variables (abs : admissible_absolute_value R)

open admissible_absolute_value

include L f abs

/-- A fraction `a / b : L` can be given as `c : integral_closure R L` divided by `d : R`. -/
lemma exists_eq_mul (a b : integral_closure R L) (hb : b ≠ 0) :
  ∃ (c : integral_closure R L) (d ≠ (0 : R)), d • a = b * c :=
begin
  have : function.injective (algebra_map R L),
  { rw is_scalar_tower.algebra_map_eq R f.codomain L,
    exact function.injective.comp (ring_hom.injective _) f.injective },
  obtain ⟨c, d, d_ne, hx⟩ := exists_integral_multiple
    (f.comap_is_algebraic_iff.mpr algebra.is_algebraic_of_finite (a / b : L))
    this,
  use [c, d, d_ne],
  apply subtype.coe_injective,
  push_cast,
  have hb' : (b : L) ≠ 0 := λ h, hb (subtype.coe_injective h),
  rw [← hx, algebra.mul_smul_comm, mul_div_cancel' (a : L) hb'],
end

/-- The `M` from the proof of thm 5.4.

Should really be `abs.card (nat.ceil_nth_root _ _)`, but nth_root _ x ≤ x so this works too.
-/
noncomputable def cardM : ℕ := abs.card (norm_bound L f abs ^ (-1 / (integral_closure.dim L f) : ℝ))

variables [infinite R]

/-- In the following results, we need a large set of distinct elements of `R`. -/
noncomputable def distinct_elems : fin (cardM L f abs ^ integral_closure.dim L f).succ ↪ R :=
function.embedding.trans (fin.coe_embedding _).to_embedding (infinite.nat_embedding R)

/-- `finset_approx` is a finite set that approximates the elements of each fractional ideal. -/
noncomputable def finset_approx [decidable_eq R] : finset R :=
((finset.univ.product finset.univ)
  .image (λ (xy : fin _ × fin _), distinct_elems L f abs xy.1 - distinct_elems L f abs xy.2))
  .erase 0

lemma finset_approx.zero_not_mem [decidable_eq R] : (0 : R) ∉ finset_approx L f abs :=
finset.not_mem_erase _ _

@[simp] lemma mem_finset_approx [decidable_eq R] {x : R} :
  x ∈ finset_approx L f abs ↔
  ∃ i j, i ≠ j ∧ distinct_elems L f abs i - distinct_elems L f abs j = x :=
begin
  simp only [finset_approx, finset.mem_erase, finset.mem_image],
  split,
  { rintros ⟨hx, ⟨i, j⟩, _, rfl⟩,
    refine ⟨i, j, _, rfl⟩,
    rintro rfl,
    simpa using hx },
  { rintros ⟨i, j, hij, rfl⟩,
    refine ⟨_, ⟨i, j⟩, finset.mem_product.mpr ⟨finset.mem_univ _, finset.mem_univ _⟩, rfl⟩,
    rw [ne.def, sub_eq_zero],
    exact λ h, hij ((distinct_elems L f abs).injective h) }
end

local attribute [-instance] real.decidable_eq

-- Theorem 5.4
theorem exists_mem_finset_approx [decidable_eq R]
  (a : integral_closure R L) {b} (hb : b ≠ (0 : R)) :
  ∃ (q : integral_closure R L) (r ∈ finset_approx L f abs),
    abs_norm f abs (r • a - b • q) < abs_norm f abs (algebra_map R (integral_closure R L) b) :=
begin
  set ε : ℝ := norm_bound L f abs ^ (-1 / (integral_closure.dim L f) : ℝ) with ε_eq,
  have hε : 0 < ε := real.rpow_pos_of_pos (int.cast_pos.mpr (norm_bound_pos L f abs)) _,
  let μ : fin (cardM L f abs ^ integral_closure.dim L f).succ ↪ R := distinct_elems L f abs,
  set s := (integral_closure.is_basis L f).repr a,
  have s_eq : ∀ i, s i = (integral_closure.is_basis L f).repr a i := λ i, rfl,
  set qs := λ j i, (μ j * s i) / b,
  have q_eq : ∀ j i, qs j i = (μ j * s i) / b := λ i j, rfl,
  set rs := λ j i, (μ j * s i) % b with r_eq,
  have r_eq : ∀ j i, rs j i = (μ j * s i) % b := λ i j, rfl,
  set c := integral_closure.basis L f,
  have c_eq : ∀ i, c i = integral_closure.basis L f i := λ i, rfl,
  have μ_eq : ∀ i j, μ j * s i = b * qs j i + rs j i,
  { intros i j,
    rw [q_eq, r_eq, euclidean_domain.div_add_mod], },
  have μ_mul_a_eq : ∀ j, μ j • a = b • ∑ i, qs j i • c i + ∑ i, rs j i • c i,
  { intro j,
    rw ← sum_repr (integral_closure.is_basis L f) a,
    simp only [finset.smul_sum, ← finset.sum_add_distrib],
    refine finset.sum_congr rfl (λ i _, _),
    rw [← c_eq, ← s_eq, ← mul_smul, μ_eq, add_smul, mul_smul] },

  obtain ⟨j, k, j_ne_k, hjk⟩ := abs.exists_approx_vec (integral_closure.dim L f) hε hb (λ j i, μ j * s i),
  have hjk' : ∀ i, (abs (rs k i - rs j i) : ℝ) < abs b • ε,
  { simpa only [r_eq] using hjk },
  set q := ∑ i, (qs k i - qs j i) • c i with q_eq,
  set r := μ k - μ j with r_eq,
  refine ⟨q, r, (mem_finset_approx L f abs).mpr _, _⟩,
  { exact ⟨k, j, j_ne_k.symm, rfl⟩ },
  have : r • a - b • q = (∑ (x : fin (integral_closure.dim L f)), (rs k x • c x - rs j x • c x)),
  { simp only [r_eq, sub_smul, μ_mul_a_eq, q_eq, finset.smul_sum, ← finset.sum_add_distrib,
               ← finset.sum_sub_distrib, smul_sub],
    refine finset.sum_congr rfl (λ x _, _),
    ring },
  rw [this, abs_norm_algebra_map],

  refine int.cast_lt.mp (lt_of_lt_of_le (norm_lt L f _ (λ i, lt_of_le_of_lt _ (hjk' i))) _),
  { apply le_of_eq,
    congr,
    simp_rw [linear_map.map_sum, linear_map.map_sub, linear_map.map_smul,
             finset.sum_apply', finsupp.sub_apply, finsupp.smul_apply',
             finset.sum_sub_distrib, is_basis.repr_self_apply, smul_eq_mul, mul_boole,
             finset.sum_ite_eq', finset.mem_univ, if_true] },
  { sorry },
end
.

-- Theorem 5.4
theorem exists_mem_finset_approx' [decidable_eq R]
  (a : integral_closure R L) {b} (hb : b ≠ (0 : integral_closure R L)) :
  ∃ (q : integral_closure R L) (r ∈ finset_approx L f abs),
  abs_norm f abs (r • a - b * q) < abs_norm f abs b :=
begin
  obtain ⟨a', b', hb', h⟩ := exists_eq_mul L f abs a b hb,
  obtain ⟨q, r, hr, hqr⟩ := exists_mem_finset_approx L f abs a' hb',
  refine ⟨q, r, hr, _⟩,
  apply lt_of_mul_lt_mul_left _
    (show 0 ≤ abs_norm f abs (algebra_map R (integral_closure R L) b'), from abs.nonneg _),
  refine lt_of_le_of_lt (le_of_eq _) (mul_lt_mul hqr (le_refl (abs_norm f abs b))
    (abs.pos ((algebra.norm_ne_zero _).mpr hb)) (abs.nonneg _)),
  rw [← abs_norm_mul, ← abs_norm_mul, ← algebra.smul_def, smul_sub b', sub_mul, smul_comm, h,
      mul_comm b a', algebra.smul_mul_assoc r a' b, mul_comm b q, algebra.smul_mul_assoc b' q b]
end

end

end euclidean_domain

lemma monoid_hom.range_eq_top {G H : Type*} [group G] [group H] (f : G →* H) :
  f.range = ⊤ ↔ function.surjective f :=
⟨ λ h y, show y ∈ f.range, from h.symm ▸ subgroup.mem_top y,
  λ h, subgroup.ext (λ x, by simp [h x]) ⟩

section euclidean_domain

variables {R K L : Type*} [euclidean_domain R] [is_dedekind_domain R]
variables [field K] [field L] [decidable_eq L]
variables (f : fraction_map R K)
variables [algebra f.codomain L] [finite_dimensional f.codomain L] [is_separable f.codomain L]
variables [algebra R L] [is_scalar_tower R f.codomain L]
variables (abs : admissible_absolute_value R)

-- Lemma 5.1
lemma exists_min (I : nonzero_ideal (integral_closure R L)) :
  ∃ b ∈ I.1, b ≠ 0 ∧ ∀ c ∈ I.1, abs_norm f abs c < abs_norm f abs b → c = 0 :=
begin
  obtain ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩, min⟩ :=
    @int.exists_least_of_bdd (λ a, ∃ b ∈ I.1, b ≠ 0 ∧ abs_norm f abs b = a) _ _,
  { use [b, b_mem, b_ne_zero],
    intros c hc lt,
    by_contra c_ne_zero,
    exact not_le_of_gt lt (min _ ⟨c, hc, c_ne_zero, rfl⟩) },
  { use 0,
    rintros _ ⟨b, b_mem, b_ne_zero, rfl⟩,
    apply abs.nonneg },
  { obtain ⟨b, b_mem, b_ne_zero⟩ := I.1.ne_bot_iff.mp I.2,
    exact ⟨_, ⟨b, b_mem, b_ne_zero, rfl⟩⟩ }
end

lemma is_scalar_tower.algebra_map_injective {R S T : Type*}
  [comm_semiring R] [comm_semiring S] [comm_semiring T]
  [algebra R S] [algebra S T] [algebra R T]
  [is_scalar_tower R S T]
  (hRS : function.injective (algebra_map R S)) (hST : function.injective (algebra_map S T)) :
  function.injective (algebra_map R T) :=
by { rw is_scalar_tower.algebra_map_eq R S T, exact hST.comp hRS }

lemma subalgebra.algebra_map_injective {R S : Type*} [comm_semiring R] [comm_semiring S]
  [algebra R S] (A : subalgebra R S) (h : function.injective (algebra_map R S)) :
  function.injective (algebra_map R A) :=
begin
  intros x y hxy,
  apply h,
  simp only [is_scalar_tower.algebra_map_apply R A S],
  exact congr_arg (coe : A → S) hxy
end

lemma integral_closure.algebra_map_injective :
  function.injective (algebra_map R (integral_closure R L)) :=
(subalgebra.algebra_map_injective _
  (is_scalar_tower.algebra_map_injective
    (show function.injective (algebra_map R f.codomain), from f.injective)
    (algebra_map f.codomain L).injective))

lemma cancel_monoid_with_zero.dvd_of_mul_dvd_mul_left {G₀ : Type*} [cancel_monoid_with_zero G₀]
  {a b c : G₀} (ha : a ≠ 0) (h : a * b ∣ a * c) :
  b ∣ c :=
begin
  obtain ⟨d, hd⟩ := h,
  refine ⟨d, mul_left_cancel' ha _⟩,
  rwa mul_assoc at hd
end

lemma ideal.dvd_of_mul_dvd_mul_left {R : Type*} [integral_domain R] [is_dedekind_domain R]
  {I J K : ideal R} (hI : I ≠ ⊥)
  (h : I * J ∣ I * K) :
  J ∣ K :=
cancel_monoid_with_zero.dvd_of_mul_dvd_mul_left hI h

lemma ideal.span_singleton_ne_bot {R : Type*} [comm_ring R] {a : R} (ha : a ≠ 0) :
  ideal.span ({a} : set R) ≠ ⊥ :=
begin
  rw [ne.def, ideal.span_eq_bot],
  push_neg,
  exact ⟨a, set.mem_singleton a, ha⟩
end

lemma finset.dvd_prod {ι M : Type*} [comm_monoid M] {x : ι} {s : finset ι}
  (hx : x ∈ s) (f : ι → M) :
  f x ∣ ∏ i in s, f i :=
multiset.dvd_prod (multiset.mem_map.mpr ⟨x, hx, rfl⟩)

-- TODO: how should we make this instance? It depends on `f.codomain`.
instance : is_dedekind_domain (integral_closure R L) := sorry

-- Theorem 5.2
theorem exists_mul_eq_mul [infinite R] [decidable_eq R] (I : nonzero_ideal (integral_closure R L)) :
  ∃ (J : nonzero_ideal (integral_closure R L)),
  class_group.mk0 (integral_closure.fraction_map_of_finite_extension L f) I =
  class_group.mk0 (integral_closure.fraction_map_of_finite_extension L f) J ∧
    J.1 ∣ ideal.span {algebra_map _ _ (∏ m in finset_approx L f abs, m)} :=
begin
  set m := ∏ m in finset_approx L f abs, m with m_eq,
  obtain ⟨b, b_mem, b_ne_zero, b_min⟩ := exists_min f abs I,
  suffices : ideal.span {b} ∣ ideal.span {algebra_map _ _ m} * I.1,
  { obtain ⟨J, hJ⟩ := this,
    refine ⟨⟨J, _⟩, _, _⟩,
    { sorry },
    { rw class_group.mk0_eq_mk0_iff,
      refine ⟨algebra_map _ _ m, b, _, b_ne_zero, hJ⟩,
      refine mt ((algebra_map R _).injective_iff.mp (integral_closure.algebra_map_injective f) _) _,
      rw finset.prod_eq_zero_iff,
      push_neg,
      intros a ha a_eq,
      rw a_eq at ha,
      exact finset_approx.zero_not_mem L f abs ha },
    apply ideal.dvd_of_mul_dvd_mul_left (ideal.span_singleton_ne_bot b_ne_zero),
    rw [ideal.dvd_iff_le, ← hJ, mul_comm, m_eq],
    apply ideal.mul_mono le_rfl,
    rw [ideal.span_le, set.singleton_subset_iff],
    exact b_mem },
  rw [ideal.dvd_iff_le, ideal.mul_le],
  intros r' hr' a ha,
  rw ideal.mem_span_singleton at ⊢ hr',
  obtain ⟨q, r, r_mem, lt⟩ := exists_mem_finset_approx' L f abs a b_ne_zero,
  apply @dvd_of_mul_left_dvd _ _ q,
  simp only [algebra.smul_def] at lt,
  rw ← sub_eq_zero.mp (b_min _ (I.1.sub_mem (I.1.mul_mem_left ha) (I.1.mul_mem_left b_mem)) lt),
  refine mul_dvd_mul_right (dvd_trans (ring_hom.map_dvd _ _) hr') _,
  exact finset.dvd_prod r_mem (λ x, x)
end
.

-- Theorem 5.3
instance : fintype (class_group f) :=
_

end euclidean_domain
