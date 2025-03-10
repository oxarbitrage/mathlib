/-
Copyright (c) 2021 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import data.set.intervals.monotone
import topology.algebra.order.monotone_continuity
import topology.urysohns_bounded

/-!
# Tietze extension theorem

In this file we prove a few version of the Tietze extension theorem. The theorem says that a
continuous function `s → ℝ` defined on a closed set in a normal topological space `Y` can be
extended to a continuous function on the whole space. Moreover, if all values of the original
function belong to some (finite or infinite, open or closed) interval, then the extension can be
chosen so that it takes values in the same interval. In particular, if the original function is a
bounded function, then there exists a bounded extension of the same norm.

The proof mostly follows <https://ncatlab.org/nlab/show/Tietze+extension+theorem>. We patch a small
gap in the proof for unbounded functions, see
`exists_extension_forall_exists_le_ge_of_closed_embedding`.

## Implementation notes

We first prove the theorems for a closed embedding `e : X → Y` of a topological space into a normal
topological space, then specialize them to the case `X = s : set Y`, `e = coe`.

## Tags

Tietze extension theorem, Urysohn's lemma, normal topological space
-/

variables {X Y : Type*} [topological_space X] [topological_space Y] [normal_space Y]

open metric set filter
open_locale bounded_continuous_function topological_space
noncomputable theory

namespace bounded_continuous_function

/-- One step in the proof of the Tietze extension theorem. If `e : C(X, Y)` is a closed embedding
of a topological space into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous
function, then there exists a bounded continuous function `g : Y →ᵇ ℝ` of the norm `∥g∥ ≤ ∥f∥ / 3`
such that the distance between `g ∘ e` and `f` is at most `(2 / 3) * ∥f∥`. -/
lemma tietze_extension_step (f : X →ᵇ ℝ) (e : C(X, Y)) (he : closed_embedding e) :
  ∃ g : Y →ᵇ ℝ, ∥g∥ ≤ ∥f∥ / 3 ∧ dist (g.comp_continuous e) f ≤ (2 / 3) * ∥f∥ :=
begin
  have h3 : (0 : ℝ) < 3 := by norm_num1,
  have h23 : 0 < (2 / 3 : ℝ) := by norm_num1,
  -- In the trivial case `f = 0`, we take `g = 0`
  rcases eq_or_ne f 0 with (rfl|hf), { use 0, simp },
  replace hf : 0 < ∥f∥ := norm_pos_iff.2 hf,
  /- Otherwise, the closed sets `e '' (f ⁻¹' (Iic (-∥f∥ / 3)))` and `e '' (f ⁻¹' (Ici (∥f∥ / 3)))`
  are disjoint, hence by Urysohn's lemma there exists a function `g` that is equal to `-∥f∥ / 3`
  on the former set and is equal to `∥f∥ / 3` on the latter set. This function `g` satisfies the
  assertions of the lemma. -/
  have hf3 : -∥f∥ / 3 < ∥f∥ / 3, from (div_lt_div_right h3).2 (left.neg_lt_self hf),
  have hc₁ : is_closed (e '' (f ⁻¹' (Iic (-∥f∥ / 3)))),
    from he.is_closed_map _ (is_closed_Iic.preimage f.continuous),
  have hc₂ : is_closed (e '' (f ⁻¹' (Ici (∥f∥ / 3)))),
    from he.is_closed_map _ (is_closed_Ici.preimage f.continuous),
  have hd : disjoint (e '' (f ⁻¹' (Iic (-∥f∥ / 3)))) (e '' (f ⁻¹' (Ici (∥f∥ / 3)))),
  { refine disjoint_image_of_injective he.inj (disjoint_preimage _ _),
    rwa [Iic_disjoint_Ici, not_le] },
  rcases exists_bounded_mem_Icc_of_closed_of_le hc₁ hc₂ hd hf3.le with ⟨g, hg₁, hg₂, hgf⟩,
  refine ⟨g, _, _⟩,
  { refine (norm_le $ div_nonneg hf.le h3.le).mpr (λ y, _),
    simpa [real.norm_eq_abs, abs_le, neg_div] using hgf y },
  { refine (dist_le $ mul_nonneg h23.le hf.le).mpr (λ x, _),
    have hfx : -∥f∥ ≤ f x ∧ f x ≤ ∥f∥,
      by simpa only [real.norm_eq_abs, abs_le] using f.norm_coe_le_norm x,
    cases le_total (f x) (-∥f∥ / 3) with hle₁ hle₁,
    { calc |g (e x) - f x| = -∥f∥ / 3 - f x:
        by rw [hg₁ (mem_image_of_mem _ hle₁), abs_of_nonneg (sub_nonneg.2 hle₁)]
      ... ≤ (2 / 3) * ∥f∥ : by linarith },
    { cases le_total (f x) (∥f∥ / 3) with hle₂ hle₂,
      { simp only [neg_div] at *,
        calc dist (g (e x)) (f x) ≤ |g (e x)| + |f x| : dist_le_norm_add_norm _ _
        ... ≤ ∥f∥ / 3 + ∥f∥ / 3 :
          add_le_add (abs_le.2 $ hgf _) (abs_le.2 ⟨hle₁, hle₂⟩)
        ... = (2 / 3) * ∥f∥ : by linarith },
      { calc |g (e x) - f x| = f x - ∥f∥ / 3 :
          by rw [hg₂ (mem_image_of_mem _ hle₂), abs_sub_comm, abs_of_nonneg (sub_nonneg.2 hle₂)]
        ... ≤ (2 / 3) * ∥f∥ : by linarith } } }
end

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version with a closed
embedding and bundled composition. If `e : C(X, Y)` is a closed embedding of a topological space
into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous function, then there exists
a bounded continuous function `g : Y →ᵇ ℝ` of the same norm such that `g ∘ e = f`. -/
lemma exists_extension_norm_eq_of_closed_embedding' (f : X →ᵇ ℝ) (e : C(X, Y))
  (he : closed_embedding e) :
  ∃ g : Y →ᵇ ℝ, ∥g∥ = ∥f∥ ∧ g.comp_continuous e = f :=
begin
  /- For the proof, we iterate `tietze_extension_step`. Each time we apply it to the difference
  between the previous approximation and `f`. -/
  choose F hF_norm hF_dist using λ f : X →ᵇ ℝ, tietze_extension_step f e he,
  set g : ℕ → Y →ᵇ ℝ := λ n, (λ g, g + F (f - g.comp_continuous e))^[n] 0,
  have g0 : g 0 = 0 := rfl,
  have g_succ : ∀ n, g (n + 1) = g n + F (f - (g n).comp_continuous e),
    from λ n, function.iterate_succ_apply' _ _ _,
  have hgf : ∀ n, dist ((g n).comp_continuous e) f ≤ (2 / 3) ^ n * ∥f∥,
  { intro n, induction n with n ihn,
    { simp [g0] },
    { rw [g_succ n, add_comp_continuous, ← dist_sub_right, add_sub_cancel', pow_succ, mul_assoc],
      refine (hF_dist _).trans (mul_le_mul_of_nonneg_left _ (by norm_num1)),
      rwa ← dist_eq_norm' } },
  have hg_dist : ∀ n, dist (g n) (g (n + 1)) ≤ 1 / 3 * ∥f∥ * (2 / 3) ^ n,
  { intro n,
    calc dist (g n) (g (n + 1)) = ∥F (f - (g n).comp_continuous e)∥ :
      by rw [g_succ, dist_eq_norm', add_sub_cancel']
    ... ≤ ∥f - (g n).comp_continuous e∥ / 3 : hF_norm _
    ... = (1 / 3) * dist ((g n).comp_continuous e) f :
      by rw [dist_eq_norm', one_div, div_eq_inv_mul]
    ... ≤ (1 / 3) * ((2 / 3) ^ n * ∥f∥) :
      mul_le_mul_of_nonneg_left (hgf n) (by norm_num1)
    ... = 1 / 3 * ∥f∥ * (2 / 3) ^ n : by ac_refl },
  have hg_cau : cauchy_seq g, from cauchy_seq_of_le_geometric _ _ (by norm_num1) hg_dist,
  have : tendsto (λ n, (g n).comp_continuous e) at_top (𝓝 $ (lim at_top g).comp_continuous e),
    from ((continuous_comp_continuous e).tendsto _).comp hg_cau.tendsto_lim,
  have hge : (lim at_top g).comp_continuous e = f,
  { refine tendsto_nhds_unique this (tendsto_iff_dist_tendsto_zero.2 _),
    refine squeeze_zero (λ _, dist_nonneg) hgf _,
    rw ← zero_mul (∥f∥),
    refine (tendsto_pow_at_top_nhds_0_of_lt_1 _ _).mul tendsto_const_nhds; norm_num1 },
  refine ⟨lim at_top g, le_antisymm _ _, hge⟩,
  { rw [← dist_zero_left, ← g0],
    refine (dist_le_of_le_geometric_of_tendsto₀ _ _ (by norm_num1)
      hg_dist hg_cau.tendsto_lim).trans_eq _,
    field_simp [show (3 - 2 : ℝ) = 1, by norm_num1] },
  { rw ← hge, exact norm_comp_continuous_le _ _ }
end

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version with a closed
embedding and unbundled composition. If `e : C(X, Y)` is a closed embedding of a topological space
into a normal topological space and `f : X →ᵇ ℝ` is a bounded continuous function, then there exists
a bounded continuous function `g : Y →ᵇ ℝ` of the same norm such that `g ∘ e = f`. -/
lemma exists_extension_norm_eq_of_closed_embedding (f : X →ᵇ ℝ) {e : X → Y}
  (he : closed_embedding e) :
  ∃ g : Y →ᵇ ℝ, ∥g∥ = ∥f∥ ∧ g ∘ e = f :=
begin
  rcases exists_extension_norm_eq_of_closed_embedding' f ⟨e, he.continuous⟩ he with ⟨g, hg, rfl⟩,
  exact ⟨g, hg, rfl⟩
end

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
set. If `f` is a bounded continuous real-valued function defined on a closed set in a normal
topological space, then it can be extended to a bounded continuous function of the same norm defined
on the whole space. -/
lemma exists_norm_eq_restrict_eq_of_closed {s : set Y} (f : s →ᵇ ℝ) (hs : is_closed s) :
  ∃ g : Y →ᵇ ℝ, ∥g∥ = ∥f∥ ∧ g.restrict s = f :=
exists_extension_norm_eq_of_closed_embedding' f ((continuous_map.id _).restrict s)
  (closed_embedding_subtype_coe hs)

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
embedding and a bounded continuous function that takes values in a non-trivial closed interval.
See also `exists_extension_forall_mem_of_closed_embedding` for a more general statement that works
for any interval (finite or infinite, open or closed).

If `e : X → Y` is a closed embedding and `f : X →ᵇ ℝ` is a bounded continuous function such that
`f x ∈ [a, b]` for all `x`, where `a ≤ b`, then there exists a bounded continuous function
`g : Y →ᵇ ℝ` such that `g y ∈ [a, b]` for all `y` and `g ∘ e = f`. -/
lemma exists_extension_forall_mem_Icc_of_closed_embedding (f : X →ᵇ ℝ) {a b : ℝ} {e : X → Y}
  (hf : ∀ x, f x ∈ Icc a b) (hle : a ≤ b) (he : closed_embedding e) :
  ∃ g : Y →ᵇ ℝ, (∀ y, g y ∈ Icc a b) ∧ g ∘ e = f :=
begin
  rcases exists_extension_norm_eq_of_closed_embedding (f - const X ((a + b) / 2)) he
    with ⟨g, hgf, hge⟩,
  refine ⟨const Y ((a + b) / 2) + g, λ y, _, _⟩,
  { suffices : ∥f - const X ((a + b) / 2)∥ ≤ (b - a) / 2,
      by simpa [real.Icc_eq_closed_ball, add_mem_closed_ball_iff_norm]
        using (norm_coe_le_norm g y).trans (hgf.trans_le this),
    refine (norm_le $ div_nonneg (sub_nonneg.2 hle) zero_le_two).2 (λ x, _),
    simpa only [real.Icc_eq_closed_ball] using hf x },
  { ext x,
    have : g (e x) = f x - (a + b) / 2 := congr_fun hge x,
    simp [this] }
end

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
embedding. Let `e` be a closed embedding of a nonempty topological space `X` into a normal
topological space `Y`. Let `f` be a bounded continuous real-valued function on `X`. Then there
exists a bounded continuous function `g : Y →ᵇ ℝ` such that `g ∘ e = f` and each value `g y` belongs
to a closed interval `[f x₁, f x₂]` for some `x₁` and `x₂`.  -/
lemma exists_extension_forall_exists_le_ge_of_closed_embedding [nonempty X] (f : X →ᵇ ℝ) {e : X → Y}
  (he : closed_embedding e) :
  ∃ g : Y →ᵇ ℝ, (∀ y, ∃ x₁ x₂, g y ∈ Icc (f x₁) (f x₂)) ∧ g ∘ e = f :=
begin
  inhabit X,
  -- Put `a = ⨅ x, f x` and `b = ⨆ x, f x`
  obtain ⟨a, ha⟩ : ∃ a, is_glb (range f) a,
    from ⟨_, is_glb_cinfi (real.bounded_iff_bdd_below_bdd_above.1 f.bounded_range).1⟩,
  obtain ⟨b, hb⟩ : ∃ b, is_lub (range f) b,
    from ⟨_, is_lub_csupr (real.bounded_iff_bdd_below_bdd_above.1 f.bounded_range).2⟩,
  -- Then `f x ∈ [a, b]` for all `x`
  have hmem : ∀ x, f x ∈ Icc a b, from λ x, ⟨ha.1 ⟨x, rfl⟩, hb.1 ⟨x, rfl⟩⟩,
  -- Rule out the trivial case `a = b`
  have hle : a ≤ b := (hmem default).1.trans (hmem default).2,
  rcases hle.eq_or_lt with (rfl|hlt),
  { have : ∀ x, f x = a, by simpa using hmem,
    use const Y a, simp [this, function.funext_iff] },
  -- Put `c = (a + b) / 2`. Then `a < c < b` and `c - a = b - c`.
  set c := (a + b) / 2,
  have hac : a < c := left_lt_add_div_two.2 hlt,
  have hcb : c < b := add_div_two_lt_right.2 hlt,
  have hsub : c - a = b - c, by { simp only [c], field_simp, ring },
  /- Due to `exists_extension_forall_mem_Icc_of_closed_embedding`, there exists an extension `g`
  such that `g y ∈ [a, b]` for all `y`. However, if `a` and/or `b` do not belong to the range of
  `f`, then we need to ensure that these points do not belong to the range of `g`. This is done
  in two almost identical steps. First we deal with the case `∀ x, f x ≠ a`. -/
  obtain ⟨g, hg_mem, hgf⟩ : ∃ g : Y →ᵇ ℝ, (∀ y, ∃ x, g y ∈ Icc (f x) b) ∧ g ∘ e = f,
  { rcases exists_extension_forall_mem_Icc_of_closed_embedding f hmem hle he
      with ⟨g, hg_mem, hgf⟩,
    -- If `a ∈ range f`, then we are done.
    rcases em (∃ x, f x = a) with ⟨x, rfl⟩|ha',
    { exact ⟨g, λ y, ⟨x, hg_mem _⟩, hgf⟩ },
    /- Otherwise, `g ⁻¹' {a}` is disjoint with `range e ∪ g ⁻¹' (Ici c)`, hence there exists a
    function `dg : Y → ℝ` such that `dg ∘ e = 0`, `dg y = 0` whenever `c ≤ g y`, `dg y = c - a`
    whenever `g y = a`, and `0 ≤ dg y ≤ c - a` for all `y`.  -/
    have hd : disjoint (range e ∪ g ⁻¹' (Ici c)) (g ⁻¹' {a}),
    { refine disjoint_union_left.2 ⟨_, disjoint_preimage _ _⟩,
      { rintro _ ⟨⟨x, rfl⟩, rfl : g (e x) = a⟩,
        exact ha' ⟨x, (congr_fun hgf x).symm⟩ },
      { exact set.disjoint_singleton_right.2 hac.not_le } },
    rcases exists_bounded_mem_Icc_of_closed_of_le
      (he.closed_range.union $ is_closed_Ici.preimage g.continuous)
      (is_closed_singleton.preimage g.continuous) hd (sub_nonneg.2 hac.le)
      with ⟨dg, dg0, dga, dgmem⟩,
    replace hgf : ∀ x, (g + dg) (e x) = f x,
    { intro x, simp [dg0 (or.inl $ mem_range_self _), ← hgf] },
    refine ⟨g + dg, λ y, _, funext hgf⟩,
    { have hay : a < (g + dg) y,
      { rcases (hg_mem y).1.eq_or_lt with rfl|hlt,
        { refine (lt_add_iff_pos_right _).2 _,
          calc 0 < c - g y : sub_pos.2 hac
             ... = dg y    : (dga rfl).symm },
        { exact hlt.trans_le ((le_add_iff_nonneg_right _).2 $ (dgmem y).1) } },
      rcases ha.exists_between hay with ⟨_, ⟨x, rfl⟩, hax, hxy⟩,
      refine ⟨x, hxy.le, _⟩,
      cases le_total c (g y) with hc hc,
      { simp [dg0 (or.inr hc), (hg_mem y).2] },
      { calc g y + dg y ≤ c + (c - a) : add_le_add hc (dgmem _).2
                    ... = b           : by rw [hsub, add_sub_cancel'_right] } } },
  /- Now we deal with the case `∀ x, f x ≠ b`. The proof is the same as in the first case, with
  minor modifications that make it hard to deduplicate code. -/
  choose xl hxl hgb using hg_mem,
  rcases em (∃ x, f x = b) with ⟨x, rfl⟩|hb',
  { exact ⟨g, λ y, ⟨xl y, x, hxl y, hgb y⟩, hgf⟩ },
  have hd : disjoint (range e ∪ g ⁻¹' (Iic c)) (g ⁻¹' {b}),
  { refine disjoint_union_left.2 ⟨_, disjoint_preimage _ _⟩,
    { rintro _ ⟨⟨x, rfl⟩, rfl : g (e x) = b⟩,
      exact hb' ⟨x, (congr_fun hgf x).symm⟩ },
    { exact set.disjoint_singleton_right.2 hcb.not_le } },
  rcases exists_bounded_mem_Icc_of_closed_of_le
    (he.closed_range.union $ is_closed_Iic.preimage g.continuous)
    (is_closed_singleton.preimage g.continuous) hd (sub_nonneg.2 hcb.le)
    with ⟨dg, dg0, dgb, dgmem⟩,
  replace hgf : ∀ x, (g - dg) (e x) = f x,
  { intro x, simp [dg0 (or.inl $ mem_range_self _), ← hgf] },
  refine ⟨g - dg, λ y, _, funext hgf⟩,
  { have hyb : (g - dg) y < b,
    { rcases (hgb y).eq_or_lt with rfl|hlt,
      { refine (sub_lt_self_iff _).2 _,
        calc 0 < g y - c : sub_pos.2 hcb
           ... = dg y    : (dgb rfl).symm },
      { exact ((sub_le_self_iff _).2 (dgmem _).1).trans_lt hlt } },
    rcases hb.exists_between hyb with ⟨_, ⟨xu, rfl⟩, hyxu, hxub⟩,
    cases lt_or_le c (g y) with hc hc,
    { rcases em (a ∈ range f) with ⟨x, rfl⟩|ha',
      { refine ⟨x, xu, _, hyxu.le⟩,
        calc f x = c - (b - c) : by rw [← hsub, sub_sub_cancel]
             ... ≤ g y - dg y  : sub_le_sub hc.le (dgmem _).2 },
      { have hay : a < (g - dg) y,
        { calc a = c - (b - c)   : by rw [← hsub, sub_sub_cancel]
             ... < g y - (b - c) : sub_lt_sub_right hc _
             ... ≤ g y - dg y    : sub_le_sub_left (dgmem _).2 _ },
        rcases ha.exists_between hay with ⟨_, ⟨x, rfl⟩, ha, hxy⟩,
        exact ⟨x, xu, hxy.le, hyxu.le⟩ } },
    { refine ⟨xl y, xu, _, hyxu.le⟩,
      simp [dg0 (or.inr hc), hxl] } },
end

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
embedding. Let `e` be a closed embedding of a nonempty topological space `X` into a normal
topological space `Y`. Let `f` be a bounded continuous real-valued function on `X`. Let `t` be
a nonempty convex set of real numbers (we use `ord_connected` instead of `convex` to automatically
deduce this argument by typeclass search) such that `f x ∈ t` for all `x`. Then there exists
a bounded continuous real-valued function `g : Y →ᵇ ℝ` such that `g y ∈ t` for all `y` and
`g ∘ e = f`. -/
lemma exists_extension_forall_mem_of_closed_embedding (f : X →ᵇ ℝ) {t : set ℝ} {e : X → Y}
  [hs : ord_connected t] (hf : ∀ x, f x ∈ t) (hne : t.nonempty) (he : closed_embedding e) :
  ∃ g : Y →ᵇ ℝ, (∀ y, g y ∈ t) ∧ g ∘ e = f :=
begin
  casesI is_empty_or_nonempty X,
  { rcases hne with ⟨c, hc⟩,
    refine ⟨const Y c, λ y, hc, funext $ λ x, is_empty_elim x⟩ },
  rcases exists_extension_forall_exists_le_ge_of_closed_embedding f he with ⟨g, hg, hgf⟩,
  refine ⟨g, λ y, _, hgf⟩,
  rcases hg y with ⟨xl, xu, h⟩,
  exact hs.out (hf _) (hf _) h
end

/-- **Tietze extension theorem** for real-valued bounded continuous maps, a version for a closed
set. Let `s` be a closed set in a normal topological space `Y`. Let `f` be a bounded continuous
real-valued function on `s`. Let `t` be a nonempty convex set of real numbers (we use
`ord_connected` instead of `convex` to automatically deduce this argument by typeclass search) such
that `f x ∈ t` for all `x : s`. Then there exists a bounded continuous real-valued function
`g : Y →ᵇ ℝ` such that `g y ∈ t` for all `y` and `g.restrict s = f`. -/
lemma exists_forall_mem_restrict_eq_of_closed {s : set Y} (f : s →ᵇ ℝ) (hs : is_closed s)
  {t : set ℝ} [ord_connected t] (hf : ∀ x, f x ∈ t) (hne : t.nonempty) :
  ∃ g : Y →ᵇ ℝ, (∀ y, g y ∈ t) ∧ g.restrict s = f :=
begin
  rcases exists_extension_forall_mem_of_closed_embedding f hf hne (closed_embedding_subtype_coe hs)
    with ⟨g, hg, hgf⟩,
  exact ⟨g, hg, fun_like.coe_injective hgf⟩
end

end bounded_continuous_function

namespace continuous_map

/-- **Tietze extension theorem** for real-valued continuous maps, a version for a closed
embedding. Let `e` be a closed embedding of a nonempty topological space `X` into a normal
topological space `Y`. Let `f` be a continuous real-valued function on `X`. Let `t` be a nonempty
convex set of real numbers (we use `ord_connected` instead of `convex` to automatically deduce this
argument by typeclass search) such that `f x ∈ t` for all `x`. Then there exists a continuous
real-valued function `g : C(Y, ℝ)` such that `g y ∈ t` for all `y` and `g ∘ e = f`. -/
lemma exists_extension_forall_mem_of_closed_embedding (f : C(X, ℝ)) {t : set ℝ} {e : X → Y}
  [hs : ord_connected t] (hf : ∀ x, f x ∈ t) (hne : t.nonempty) (he : closed_embedding e) :
  ∃ g : C(Y, ℝ), (∀ y, g y ∈ t) ∧ g ∘ e = f :=
begin
  have h : ℝ ≃o Ioo (-1 : ℝ) 1 := order_iso_Ioo_neg_one_one ℝ,
  set F : X →ᵇ ℝ :=
  { to_fun := coe ∘ (h ∘ f),
    continuous_to_fun := continuous_subtype_coe.comp (h.continuous.comp f.continuous),
    map_bounded' := bounded_range_iff.1 ((bounded_Ioo (-1 : ℝ) 1).mono $
      forall_range_iff.2 $ λ x, (h (f x)).2) },
  set t' : set ℝ := (coe ∘ h) '' t,
  have ht_sub : t' ⊆ Ioo (-1 : ℝ) 1 := image_subset_iff.2 (λ x hx, (h x).2),
  haveI : ord_connected t',
  { constructor, rintros _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ z hz,
    lift z to Ioo (-1 : ℝ) 1 using (Icc_subset_Ioo (h x).2.1 (h y).2.2 hz),
    change z ∈ Icc (h x) (h y) at hz, rw [← h.image_Icc] at hz,
    rcases hz with ⟨z, hz, rfl⟩,
    exact ⟨z, hs.out hx hy hz, rfl⟩ },
  have hFt : ∀ x, F x ∈ t', from λ x, mem_image_of_mem _ (hf x),
  rcases F.exists_extension_forall_mem_of_closed_embedding hFt (hne.image _) he
    with ⟨G, hG, hGF⟩,
  set g : C(Y, ℝ) := ⟨h.symm ∘ cod_restrict G _ (λ y, ht_sub (hG y)), h.symm.continuous.comp $
    continuous_subtype_mk _ G.continuous⟩,
  have hgG : ∀ {y a}, g y = a ↔ G y = h a,
    from λ y a, h.to_equiv.symm_apply_eq.trans subtype.ext_iff,
  refine ⟨g, λ y, _, _⟩,
  { rcases hG y with ⟨a, ha, hay⟩,
    convert ha,
    exact hgG.2 hay.symm },
  { ext x, exact hgG.2 (congr_fun hGF _) }
end

/-- **Tietze extension theorem** for real-valued continuous maps, a version for a closed
embedding. Let `e` be a closed embedding of a nonempty topological space `X` into a normal
topological space `Y`. Let `f` be a continuous real-valued function on `X`. Then there exists a
continuous real-valued function `g : C(Y, ℝ)` such that `g ∘ e = f`. -/
lemma exists_extension_of_closed_embedding (f : C(X, ℝ)) (e : X → Y) (he : closed_embedding e) :
  ∃ g : C(Y, ℝ), g ∘ e = f :=
(exists_extension_forall_mem_of_closed_embedding f (λ x, mem_univ _) univ_nonempty he).imp $
  λ g, and.right

/-- **Tietze extension theorem** for real-valued continuous maps, a version for a closed set. Let
`s` be a closed set in a normal topological space `Y`. Let `f` be a continuous real-valued function
on `s`. Let `t` be a nonempty convex set of real numbers (we use `ord_connected` instead of `convex`
to automatically deduce this argument by typeclass search) such that `f x ∈ t` for all `x : s`. Then
there exists a continuous real-valued function `g : C(Y, ℝ)` such that `g y ∈ t` for all `y` and
`g.restrict s = f`. -/
lemma exists_restrict_eq_forall_mem_of_closed {s : set Y} (f : C(s, ℝ)) {t : set ℝ}
  [ord_connected t] (ht : ∀ x, f x ∈ t) (hne : t.nonempty) (hs : is_closed s) :
  ∃ g : C(Y, ℝ), (∀ y, g y ∈ t) ∧ g.restrict s = f :=
let ⟨g, hgt, hgf⟩ := exists_extension_forall_mem_of_closed_embedding f ht hne
  (closed_embedding_subtype_coe hs)
in ⟨g, hgt, coe_injective hgf⟩

/-- **Tietze extension theorem** for real-valued continuous maps, a version for a closed set. Let
`s` be a closed set in a normal topological space `Y`. Let `f` be a continuous real-valued function
on `s`. Then there exists a continuous real-valued function `g : C(Y, ℝ)` such that
`g.restrict s = f`. -/
lemma exists_restrict_eq_of_closed {s : set Y} (f : C(s, ℝ)) (hs : is_closed s) :
  ∃ g : C(Y, ℝ), g.restrict s = f :=
let ⟨g, hg, hgf⟩ := exists_restrict_eq_forall_mem_of_closed f (λ _, mem_univ _) univ_nonempty hs
in ⟨g, hgf⟩

end continuous_map
