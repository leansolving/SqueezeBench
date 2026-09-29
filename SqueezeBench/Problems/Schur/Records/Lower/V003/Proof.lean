import SqueezeBench.Problems.Schur.Records.Lower.V003.Def
import SqueezeBench.Problems.Schur.Records.Lower.V002.Proof

/-! Record V003 for Schur, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Schur/Lower/V003.lean`.

Two additions to V002's dynamic programme. (1) The **shifted S-template** step
`S(k+2) ≥ 10·S(k) + 2` of Bengone, Brouk, Grinsztajn, Helbert, Lugherini, Rimmel, Tomasik,
arXiv:2607.15034 (2026): the theorem `sf_shApply` is proved for an abstract template with shift
set `{−1, 0}` and a tail, whose admissibility `Adm` is a finite check over column pairs and
first-row flags, evaluated by the kernel as the `Bool` `admCheck`; the width-10 template of the
paper (Table II) is `lab10`/`labF10` with tail `[A, B]`. (2) The base `S(7) ≥ 1696` of Rowley,
arXiv:2107.03560, as bitsets checked by V002's `sf_colOf`. Everything else (sum-free colourings
`V002.SF`, the S-template steps, the bitset checkers) is reused from V002. -/

namespace SqueezeBench.Schur.Lower.V003

open SqueezeBench Finset

/-! ### Shifted S-templates with shifts `{0, −1}` and a tail

Bengone, Brouk, Grinsztajn, Helbert, Lugherini, Rimmel, Tomasik, *Shifted S-templates and
improved lower bounds for Schur numbers*, arXiv:2607.15034 (2026), Definition 1 and Theorem 2,
for the shift set `{−1, 0}`. Rows of width `q` are laid over a base colouring `g` of `[1, p]`;
column `u` carries a label: an ordinary new colour `< r`, or `r` ("the base colour of this row"),
or `r + 1` ("the base colour of the row above"); the first row has its own labels (never `r + 1`),
and a tail of ordinary colours follows the `p` rows. -/

-- The label of column `u` in a first row (`f = 1`) or in any other row.
def slab (lab labF : ℕ → ℕ) (f u : ℕ) : ℕ := if f = 1 then labF u else lab u

-- The colour of the cell in row `a + 1` (a first row iff `a = 0`), column `u`.
def cellCol (lab labF : ℕ → ℕ) (r : ℕ) (g : ℕ → ℕ) (k a u : ℕ) : ℕ :=
  if slab lab labF (if a = 0 then 1 else 0) u < r then k + slab lab labF (if a = 0 then 1 else 0) u
  else if slab lab labF (if a = 0 then 1 else 0) u = r then g (a + 1) else g a

-- `p` rows of width `q` over `g`, then the tail.
def shApply (lab labF : ℕ → ℕ) (q r : ℕ) (tail : List ℕ) (g : ℕ → ℕ) (k p x : ℕ) : ℕ :=
  if x ≤ q * p then cellCol lab labF r g k ((x - 1) / q) ((x - 1) % q + 1)
  else k + tail.getD (x - q * p - 1) 0

-- The carry of a column sum.
def carry (q u v : ℕ) : ℕ := if q < u + v then 1 else 0

-- The first-row flag of the sum of a row with flag `fa` and a row with flag `fb`.
def sumFlag (q u v fa fb : ℕ) : ℕ := if fa = 1 ∧ fb = 1 ∧ carry q u v = 0 then 1 else 0

-- Admissibility: a finite check over column pairs and first-row flags. Ordinary triples are never
-- monochromatic; a triple of shifted labels `r + a`, `r + b`, `r + c` has `c + 1 = a + b + carry`,
-- so the three base cells form `x' + y' = z'`; and the tail creates no monochromatic sum.
def Adm (lab labF : ℕ → ℕ) (q r : ℕ) (tail : List ℕ) : Prop :=
  1 ≤ q ∧ tail.length ≤ q ∧
  (∀ u < q + 1, 1 ≤ u → lab u ≤ r + 1 ∧ labF u ≤ r) ∧
  (∀ j < tail.length, tail.getD j 0 < r) ∧
  (∀ u < q + 1, ∀ v < q + 1, ∀ fa < 2, ∀ fb < 2, (1 ≤ u ∧ 1 ≤ v) →
    (slab lab labF fa u < r ∧ slab lab labF fa u = slab lab labF fb v →
      slab lab labF (sumFlag q u v fa fb) (u + v - carry q u v * q) ≠ slab lab labF fa u) ∧
    (r ≤ slab lab labF fa u ∧ r ≤ slab lab labF fb v ∧
        r ≤ slab lab labF (sumFlag q u v fa fb) (u + v - carry q u v * q) →
      slab lab labF (sumFlag q u v fa fb) (u + v - carry q u v * q) - r + 1
        = (slab lab labF fa u - r) + (slab lab labF fb v - r) + carry q u v)) ∧
  (∀ u < q + 1, ∀ v < q + 1, ∀ fa < 2, ∀ fb < 2, ∀ j < tail.length,
    (1 ≤ u ∧ 1 ≤ v ∧ u + v - carry q u v * q = j + 1 ∧ ((fa = 1 ∨ fb = 1) → carry q u v = 1)) →
    ¬ (slab lab labF fa u < r ∧ slab lab labF fa u = slab lab labF fb v ∧
        slab lab labF fb v = tail.getD j 0)) ∧
  (∀ i < tail.length, ∀ j < tail.length, i < j →
    ¬ (tail.getD i 0 = tail.getD j 0 ∧ slab lab labF 1 (j - i) = tail.getD i 0))

-- The same check as a `Bool`, evaluated by the kernel (`List.all` loops instead of nested
-- bounded quantifiers, whose `Decidable` instances Lean fails to synthesise at this depth).
def admCheck (lab labF : ℕ → ℕ) (q r : ℕ) (tail : List ℕ) : Bool :=
  decide (1 ≤ q) && decide (tail.length ≤ q) &&
  (List.range (q + 1)).all (fun u => decide (1 ≤ u → lab u ≤ r + 1 ∧ labF u ≤ r)) &&
  (List.range tail.length).all (fun j => decide (tail.getD j 0 < r)) &&
  (List.range (q + 1)).all (fun u => (List.range (q + 1)).all (fun v =>
    (List.range 2).all (fun fa => (List.range 2).all (fun fb => decide ((1 ≤ u ∧ 1 ≤ v) →
      (slab lab labF fa u < r ∧ slab lab labF fa u = slab lab labF fb v →
        slab lab labF (sumFlag q u v fa fb) (u + v - carry q u v * q) ≠ slab lab labF fa u) ∧
      (r ≤ slab lab labF fa u ∧ r ≤ slab lab labF fb v ∧
          r ≤ slab lab labF (sumFlag q u v fa fb) (u + v - carry q u v * q) →
        slab lab labF (sumFlag q u v fa fb) (u + v - carry q u v * q) - r + 1
          = (slab lab labF fa u - r) + (slab lab labF fb v - r) + carry q u v)))))) &&
  (List.range (q + 1)).all (fun u => (List.range (q + 1)).all (fun v =>
    (List.range 2).all (fun fa => (List.range 2).all (fun fb =>
      (List.range tail.length).all (fun j => decide
        ((1 ≤ u ∧ 1 ≤ v ∧ u + v - carry q u v * q = j + 1 ∧ ((fa = 1 ∨ fb = 1) → carry q u v = 1)) →
        ¬ (slab lab labF fa u < r ∧ slab lab labF fa u = slab lab labF fb v ∧
            slab lab labF fb v = tail.getD j 0))))))) &&
  (List.range tail.length).all (fun i => (List.range tail.length).all (fun j => decide (i < j →
    ¬ (tail.getD i 0 = tail.getD j 0 ∧ slab lab labF 1 (j - i) = tail.getD i 0))))

theorem adm_of_check {lab labF : ℕ → ℕ} {q r : ℕ} {tail : List ℕ}
    (h : admCheck lab labF q r tail = true) : Adm lab labF q r tail := by
  unfold admCheck at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem slab_le {lab labF : ℕ → ℕ} {r fa u : ℕ} (hlab : lab u ≤ r + 1 ∧ labF u ≤ r) :
    slab lab labF fa u ≤ r + 1 := by
  rw [slab]; split_ifs <;> omega

-- A label `r + 1` never sits in a first row.
theorem slab_succ_row {lab labF : ℕ → ℕ} {r fa u α : ℕ} (hlab : lab u ≤ r + 1 ∧ labF u ≤ r)
    (hfa : fa = if α = 0 then 1 else 0) (h : slab lab labF fa u = r + 1) : 1 ≤ α := by
  rw [slab] at h
  split_ifs at h with hf
  · omega
  · rw [hfa] at hf; split_ifs at hf with h0 <;> omega

-- The colour of a cell: an ordinary colour, the base colour of its row, or of the row above.
theorem cellCol_cases {lab labF : ℕ → ℕ} {r : ℕ} {g : ℕ → ℕ} {k a u fa : ℕ}
    (hlab : lab u ≤ r + 1 ∧ labF u ≤ r) (hfa : fa = if a = 0 then 1 else 0) :
    (slab lab labF fa u < r ∧ cellCol lab labF r g k a u = k + slab lab labF fa u) ∨
    (slab lab labF fa u = r ∧ cellCol lab labF r g k a u = g (a + 1)) ∨
    (slab lab labF fa u = r + 1 ∧ 1 ≤ a ∧ cellCol lab labF r g k a u = g a) := by
  subst hfa
  by_cases h1 : slab lab labF (if a = 0 then 1 else 0) u < r
  · exact Or.inl ⟨h1, by rw [cellCol, if_pos h1]⟩
  by_cases h2 : slab lab labF (if a = 0 then 1 else 0) u = r
  · exact Or.inr (Or.inl ⟨h2, by rw [cellCol, if_neg h1, if_pos h2]⟩)
  have h3 : slab lab labF (if a = 0 then 1 else 0) u = r + 1 := by
    have := slab_le (fa := if a = 0 then 1 else 0) hlab; omega
  exact Or.inr (Or.inr ⟨h3, slab_succ_row hlab rfl h3, by rw [cellCol, if_neg h1, if_neg h2]⟩)

theorem cellCol_lt {lab labF : ℕ → ℕ} {r : ℕ} {g : ℕ → ℕ} {k p a u : ℕ}
    (hlab : lab u ≤ r + 1 ∧ labF u ≤ r) (hg : ∀ x, 1 ≤ x → x ≤ p → g x < k) (ha : a + 1 ≤ p) :
    cellCol lab labF r g k a u < k + r := by
  rcases cellCol_cases (g := g) (k := k) (a := a) hlab rfl with ⟨h, hc⟩ | ⟨h, hc⟩ | ⟨h, h1, hc⟩
  · omega
  · have := hg (a + 1) (by omega) ha; omega
  · have := hg a h1 (by omega); omega

-- Row `a` (zero-based) of `x ∈ [1, qp]` is below `p`.
theorem row_lt {q p x : ℕ} (hq : 0 < q) (hx : 1 ≤ x) (hxp : x ≤ q * p) : (x - 1) / q + 1 ≤ p := by
  have : (x - 1) / q < p := by
    rw [Nat.div_lt_iff_lt_mul hq]
    have := Nat.mul_comm p q
    omega
  omega

theorem sf_close {k p : ℕ} {g : ℕ → ℕ} (hg : V002.SF k p g) {X Y Z : ℕ} (hX : 1 ≤ X)
    (hY : 1 ≤ Y) (hZ : Z ≤ p) (hXYZ : X + Y = Z) (hc : g X = g Y) (hz : g Z = g X) : False := by
  subst hXYZ; exact hg.2 X Y hX hY hZ hc hz

-- Three cells of the block with `x + y = z` are never monochromatic.
theorem block_case {lab labF : ℕ → ℕ} {r k p : ℕ} {g : ℕ → ℕ} (hg : V002.SF k p g)
    {u v w α β e fa fb fc : ℕ}
    (hlu : lab u ≤ r + 1 ∧ labF u ≤ r) (hlv : lab v ≤ r + 1 ∧ labF v ≤ r)
    (hlw : lab w ≤ r + 1 ∧ labF w ≤ r)
    (hfa : fa = if α = 0 then 1 else 0) (hfb : fb = if β = 0 then 1 else 0)
    (hfc : fc = if α + β + e = 0 then 1 else 0)
    (hm1 : slab lab labF fa u < r ∧ slab lab labF fa u = slab lab labF fb v →
      slab lab labF fc w ≠ slab lab labF fa u)
    (hm2 : r ≤ slab lab labF fa u ∧ r ≤ slab lab labF fb v ∧ r ≤ slab lab labF fc w →
      slab lab labF fc w - r + 1 = (slab lab labF fa u - r) + (slab lab labF fb v - r) + e)
    (hαp : α + 1 ≤ p) (hβp : β + 1 ≤ p) (hγp : α + β + e + 1 ≤ p)
    (hc : cellCol lab labF r g k α u = cellCol lab labF r g k β v)
    (hz : cellCol lab labF r g k (α + β + e) w = cellCol lab labF r g k α u) : False := by
  have hga := hg.1
  have gb1 : g (α + 1) < k := hga _ (by omega) hαp
  have gb2 : g (β + 1) < k := hga _ (by omega) hβp
  have gb3 : 1 ≤ α → g α < k := fun h => hga α h (by omega)
  have gb4 : 1 ≤ β → g β < k := fun h => hga β h (by omega)
  have gb5 : g (α + β + e + 1) < k := hga _ (by omega) hγp
  have gb6 : 1 ≤ α + β + e → g (α + β + e) < k := fun h => hga _ h (by omega)
  rcases cellCol_cases (g := g) (k := k) hlu hfa with ⟨hxa, hxc⟩ | ⟨hxa, hxc⟩ | ⟨hxa, hα1, hxc⟩ <;>
  rcases cellCol_cases (g := g) (k := k) hlv hfb with ⟨hya, hyc⟩ | ⟨hya, hyc⟩ | ⟨hya, hβ1, hyc⟩ <;>
  rcases cellCol_cases (g := g) (k := k) hlw hfc with ⟨hza, hzc⟩ | ⟨hza, hzc⟩ | ⟨hza, hγ1, hzc⟩ <;>
  rw [hxc, hyc] at hc <;> rw [hzc, hxc] at hz <;>
  first
    | omega
    | (have hrel := hm2 ⟨by omega, by omega, by omega⟩
       exact sf_close hg (by omega) (by omega) (by omega) (by omega) hc hz)

-- Two cells of the block whose sum lands on a tail cell of ordinary colour `t`.
theorem tail_case {lab labF : ℕ → ℕ} {r k p : ℕ} {g : ℕ → ℕ} (hg : V002.SF k p g)
    {u v α β fa fb t : ℕ}
    (hlu : lab u ≤ r + 1 ∧ labF u ≤ r) (hlv : lab v ≤ r + 1 ∧ labF v ≤ r)
    (hfa : fa = if α = 0 then 1 else 0) (hfb : fb = if β = 0 then 1 else 0)
    (hαp : α + 1 ≤ p) (hβp : β + 1 ≤ p)
    (hm : ¬ (slab lab labF fa u < r ∧ slab lab labF fa u = slab lab labF fb v ∧
      slab lab labF fb v = t))
    (hc : cellCol lab labF r g k α u = cellCol lab labF r g k β v)
    (hz : cellCol lab labF r g k α u = k + t) : False := by
  have hga := hg.1
  have gb1 : g (α + 1) < k := hga _ (by omega) hαp
  have gb2 : g (β + 1) < k := hga _ (by omega) hβp
  have gb3 : 1 ≤ α → g α < k := fun h => hga α h (by omega)
  have gb4 : 1 ≤ β → g β < k := fun h => hga β h (by omega)
  rcases cellCol_cases (g := g) (k := k) hlu hfa with ⟨hxa, hxc⟩ | ⟨hxa, hxc⟩ | ⟨hxa, hα1, hxc⟩ <;>
  rcases cellCol_cases (g := g) (k := k) hlv hfb with ⟨hya, hyc⟩ | ⟨hya, hyc⟩ | ⟨hya, hβ1, hyc⟩ <;>
  rw [hxc, hyc] at hc <;> rw [hxc] at hz <;> omega

theorem sf_shApply {lab labF : ℕ → ℕ} {q r : ℕ} {tail : List ℕ} (hadm : Adm lab labF q r tail)
    {k p : ℕ} {g : ℕ → ℕ} (hg : V002.SF k p g) (hp : 1 ≤ p) :
    V002.SF (k + r) (q * p + tail.length) (shApply lab labF q r tail g k p) := by
  obtain ⟨hq1, htq, hlab, htail, hmain, htail1, htail2⟩ := hadm
  have hq : 0 < q := hq1
  have hcol : ∀ x, 1 ≤ (x - 1) % q + 1 ∧ (x - 1) % q + 1 ≤ q := fun x =>
    ⟨by omega, by have := Nat.mod_lt (x - 1) hq; omega⟩
  have hga : ∀ t, 1 ≤ t → t ≤ p → g t < k := hg.1
  refine ⟨fun x hx hxN => ?_, fun x y hx hy hxy hc hz => ?_⟩
  · unfold shApply
    split_ifs with hxp
    · exact cellCol_lt (hlab _ (by have := hcol x; omega) (hcol x).1) hg.1 (row_lt hq hx hxp)
    · have := htail (x - q * p - 1) (by omega)
      omega
  · by_cases hzp : x + y ≤ q * p
    · -- the sum lies in the block, hence so do `x` and `y`
      have hxp : x ≤ q * p := by omega
      have hyp : y ≤ q * p := by omega
      obtain ⟨u, hu⟩ : ∃ u, u = (x - 1) % q + 1 := ⟨_, rfl⟩
      obtain ⟨v, hv⟩ : ∃ v, v = (y - 1) % q + 1 := ⟨_, rfl⟩
      obtain ⟨α, hα⟩ : ∃ α, α = (x - 1) / q := ⟨_, rfl⟩
      obtain ⟨β, hβ⟩ : ∃ β, β = (y - 1) / q := ⟨_, rfl⟩
      have hu1 : 1 ≤ u ∧ u ≤ q := hu ▸ hcol x
      have hv1 : 1 ≤ v ∧ v ≤ q := hv ▸ hcol y
      have hrc := V002.row_col_add hq hx hy
      rw [← hu, ← hv, ← hα, ← hβ] at hrc
      have hαp : α + 1 ≤ p := hα ▸ row_lt hq hx hxp
      have hβp : β + 1 ≤ p := hβ ▸ row_lt hq hy hyp
      have hγp : (x + y - 1) / q + 1 ≤ p := row_lt hq (by omega) hzp
      have ex : shApply lab labF q r tail g k p x = cellCol lab labF r g k α u := by
        rw [shApply, if_pos hxp, ← hu, ← hα]
      have ey : shApply lab labF q r tail g k p y = cellCol lab labF r g k β v := by
        rw [shApply, if_pos hyp, ← hv, ← hβ]
      have ez : shApply lab labF q r tail g k p (x + y) =
          cellCol lab labF r g k ((x + y - 1) / q) ((x + y - 1) % q + 1) := by
        rw [shApply, if_pos hzp]
      obtain ⟨e, he⟩ : ∃ e, e = carry q u v := ⟨_, rfl⟩
      have hw : (x + y - 1) % q + 1 = u + v - e * q := by
        rcases Nat.lt_or_ge q (u + v) with hgt | hle
        · have : e = 1 := by rw [he, carry, if_pos hgt]
          rw [this, (hrc.2 hgt).1]; omega
        · have : e = 0 := by rw [he, carry, if_neg (by omega)]
          rw [this, (hrc.1 hle).1]; omega
      have hγ : (x + y - 1) / q = α + β + e := by
        rcases Nat.lt_or_ge q (u + v) with hgt | hle
        · have : e = 1 := by rw [he, carry, if_pos hgt]
          rw [this, (hrc.2 hgt).2]
        · have : e = 0 := by rw [he, carry, if_neg (by omega)]
          rw [this, (hrc.1 hle).2]; omega
      have hγp' : α + β + e + 1 ≤ p := by rw [← hγ]; exact hγp
      obtain ⟨fa, hfa⟩ : ∃ fa, fa = if α = 0 then 1 else 0 := ⟨_, rfl⟩
      obtain ⟨fb, hfb⟩ : ∃ fb, fb = if β = 0 then 1 else 0 := ⟨_, rfl⟩
      have hfa2 : fa < 2 := by rw [hfa]; split <;> omega
      have hfb2 : fb < 2 := by rw [hfb]; split <;> omega
      have hfc : (if α + β + e = 0 then 1 else 0) = sumFlag q u v fa fb := by
        rw [sumFlag, ← he, hfa, hfb]
        by_cases ha0 : α = 0 <;> by_cases hb0 : β = 0 <;> by_cases he0 : e = 0 <;>
          simp [ha0, hb0, he0]
      have hlu := hlab u (by omega) hu1.1
      have hlv := hlab v (by omega) hv1.1
      have hlw := hlab (u + v - e * q) (by omega) (by omega)
      have hm := hmain u (by omega) v (by omega) fa hfa2 fb hfb2 ⟨hu1.1, hv1.1⟩
      rw [← he] at hm
      rw [ex, ey] at hc
      rw [ez, ex, hw, hγ] at hz
      exact block_case hg hlu hlv hlw hfa hfb hfc.symm hm.1 hm.2 hαp hβp hγp' hc hz
    · -- the sum lies in the tail
      obtain ⟨j, hj⟩ : ∃ j, x + y = q * p + j + 1 := ⟨x + y - q * p - 1, by omega⟩
      have hjt : j < tail.length := by omega
      have ez : shApply lab labF q r tail g k p (x + y) = k + tail.getD j 0 := by
        rw [shApply, if_neg hzp]
        congr 2
        omega
      rw [ez] at hz
      have htj := htail j hjt
      by_cases hxp : x ≤ q * p
      · by_cases hyp : y ≤ q * p
        · -- both summands in the block
          obtain ⟨u, hu⟩ : ∃ u, u = (x - 1) % q + 1 := ⟨_, rfl⟩
          obtain ⟨v, hv⟩ : ∃ v, v = (y - 1) % q + 1 := ⟨_, rfl⟩
          obtain ⟨α, hα⟩ : ∃ α, α = (x - 1) / q := ⟨_, rfl⟩
          obtain ⟨β, hβ⟩ : ∃ β, β = (y - 1) / q := ⟨_, rfl⟩
          have hu1 : 1 ≤ u ∧ u ≤ q := hu ▸ hcol x
          have hv1 : 1 ≤ v ∧ v ≤ q := hv ▸ hcol y
          have hrc := V002.row_col_add hq hx hy
          rw [← hu, ← hv, ← hα, ← hβ] at hrc
          have hαp : α + 1 ≤ p := hα ▸ row_lt hq hx hxp
          have hβp : β + 1 ≤ p := hβ ▸ row_lt hq hy hyp
          have ex : shApply lab labF q r tail g k p x = cellCol lab labF r g k α u := by
            rw [shApply, if_pos hxp, ← hu, ← hα]
          have ey : shApply lab labF q r tail g k p y = cellCol lab labF r g k β v := by
            rw [shApply, if_pos hyp, ← hv, ← hβ]
          obtain ⟨e, he⟩ : ∃ e, e = carry q u v := ⟨_, rfl⟩
          have hw : (x + y - 1) % q + 1 = u + v - e * q := by
            rcases Nat.lt_or_ge q (u + v) with hgt | hle
            · have : e = 1 := by rw [he, carry, if_pos hgt]
              rw [this, (hrc.2 hgt).1]; omega
            · have : e = 0 := by rw [he, carry, if_neg (by omega)]
              rw [this, (hrc.1 hle).1]; omega
          have hγ : (x + y - 1) / q = α + β + e := by
            rcases Nat.lt_or_ge q (u + v) with hgt | hle
            · have : e = 1 := by rw [he, carry, if_pos hgt]
              rw [this, (hrc.2 hgt).2]
            · have : e = 0 := by rw [he, carry, if_neg (by omega)]
              rw [this, (hrc.1 hle).2]; omega
          -- the sum sits in row `p + 1`, column `j + 1`
          have hzq : (x + y - 1) / q = p ∧ (x + y - 1) % q = j := by
            have h1 : x + y - 1 = j + q * p := by omega
            rw [h1, Nat.add_mul_div_left _ _ hq, Nat.add_mul_mod_self_left,
              Nat.div_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
            omega
          have hwj : u + v - e * q = j + 1 := by rw [← hw, hzq.2]
          have hpe : α + β + e = p := by rw [← hγ, hzq.1]
          obtain ⟨fa, hfa⟩ : ∃ fa, fa = if α = 0 then 1 else 0 := ⟨_, rfl⟩
          obtain ⟨fb, hfb⟩ : ∃ fb, fb = if β = 0 then 1 else 0 := ⟨_, rfl⟩
          have hfa2 : fa < 2 := by rw [hfa]; split <;> omega
          have hfb2 : fb < 2 := by rw [hfb]; split <;> omega
          have he1 : e ≤ 1 := by rw [he, carry]; split <;> omega
          have hex : (fa = 1 ∨ fb = 1) → e = 1 := by
            intro h
            rcases h with h | h
            · rw [hfa] at h; split_ifs at h with h0; omega
            · rw [hfb] at h; split_ifs at h with h0; omega
          have hm := htail1 u (by omega) v (by omega) fa hfa2 fb hfb2 j hjt
            ⟨hu1.1, hv1.1, by rw [← he]; exact hwj, by rw [← he]; exact hex⟩
          have hlu := hlab u (by omega) hu1.1
          have hlv := hlab v (by omega) hv1.1
          rw [ex, ey] at hc
          rw [ex] at hz
          exact tail_case hg hlu hlv hfa hfb hαp hβp hm hc hz.symm
        · -- `y` in the tail, `x` in the first row
          obtain ⟨i, hi⟩ : ∃ i, y = q * p + i + 1 := ⟨y - q * p - 1, by omega⟩
          have hij : i < j := by omega
          have hxji : x = j - i := by omega
          have ey : shApply lab labF q r tail g k p y = k + tail.getD i 0 := by
            rw [shApply, if_neg hyp]; congr 2; omega
          have ex : shApply lab labF q r tail g k p x = cellCol lab labF r g k 0 x := by
            rw [shApply, if_pos hxp]
            have h1 : (x - 1) / q = 0 := Nat.div_eq_of_lt (by omega)
            have h2 : (x - 1) % q + 1 = x := by rw [Nat.mod_eq_of_lt (by omega)]; omega
            rw [h1, h2]
          have hlx := hlab x (by omega) hx
          rw [ex, ey] at hc
          rw [ex] at hz
          rcases cellCol_cases (g := g) (k := k) (a := 0) (fa := 1) hlx rfl with
            ⟨hxa, hxc⟩ | ⟨hxa, hxc⟩ | ⟨hxa, hα1, hxc⟩ <;>
          rw [hxc] at hc hz
          · exact htail2 i (by omega) j hjt hij ⟨by omega, by rw [← hxji]; omega⟩
          · have := hga (0 + 1) (by omega) (by omega); omega
          · omega
      · by_cases hyp : y ≤ q * p
        · -- `x` in the tail, `y` in the first row
          obtain ⟨i, hi⟩ : ∃ i, x = q * p + i + 1 := ⟨x - q * p - 1, by omega⟩
          have hij : i < j := by omega
          have hyji : y = j - i := by omega
          have ex : shApply lab labF q r tail g k p x = k + tail.getD i 0 := by
            rw [shApply, if_neg hxp]; congr 2; omega
          have ey : shApply lab labF q r tail g k p y = cellCol lab labF r g k 0 y := by
            rw [shApply, if_pos hyp]
            have h1 : (y - 1) / q = 0 := Nat.div_eq_of_lt (by omega)
            have h2 : (y - 1) % q + 1 = y := by rw [Nat.mod_eq_of_lt (by omega)]; omega
            rw [h1, h2]
          have hly := hlab y (by omega) hy
          rw [ex, ey] at hc
          rw [ex] at hz
          rcases cellCol_cases (g := g) (k := k) (a := 0) (fa := 1) hly rfl with
            ⟨hya, hyc⟩ | ⟨hya, hyc⟩ | ⟨hya, hβ1, hyc⟩ <;>
          rw [hyc] at hc
          · exact htail2 i (by omega) j hjt hij ⟨by omega, by rw [← hyji]; omega⟩
          · have := hga (0 + 1) (by omega) (by omega); omega
          · omega
        · -- both in the tail: impossible
          exfalso
          have : q ≤ q * p := Nat.le_mul_of_pos_right q hp
          omega


/-! ### The width-10 shifted template (arXiv:2607.15034, Table II), and Rowley's `[1, 1696]`

Labels: `0 = A`, `1 = B` (the two new colours), `2 = P₀`, `3 = P₋₁`. Generic rows read
`P₋₁ B P₀ P₀ B A A B P₀ P₀`, the first row `B A P₀ P₀ B A A B P₀ P₀`, the tail `A B`.
`P1696` is the sum-free 7-partition of `[1, 1696]` of F. Rowley, *An improved lower bound for
S(7) and some interesting templates*, arXiv:2107.03560 (ancillary spreadsheet), as bitsets. -/

def lab10 (u : ℕ) : ℕ := [3, 1, 2, 2, 1, 0, 0, 1, 2, 2].getD (u - 1) 0

def labF10 (u : ℕ) : ℕ := [1, 0, 2, 2, 1, 0, 0, 1, 2, 2].getD (u - 1) 0

theorem adm10 : Adm lab10 labF10 10 2 [0, 1] := adm_of_check (by decide +kernel)

-- The shifted-template step `S(k+2) ≥ 10·S(k) + 2`.
theorem step10 {k N : ℕ} (h : V002.Good k N) (hN : 1 ≤ N) : V002.Good (k + 2) (10 * N + 2) := by
  obtain ⟨g, hg⟩ := h
  exact ⟨_, sf_shApply adm10 hg hN⟩

def P1696 : List ℕ := [41926590455258599234852784196623622266014569368089195231247092578127926869100751388211477414005388294036970069948701900152565692050811660478060450453912235089987267681671397103871455380419275810363100042732401588249681552166454170322932234425687914044576549885920208090636703447966467915486429409465413076677725227180358919899093290803580172310844197199326356731308436496858753089290683833376909765699032026326506816040361686344143526984009532292019006405612311192872801476937205674585825491510286636573311744, 881610411606792348511129896876854050584038076762660715309289651055106874576981463849346290826130107880694634152495073165267901958843852770334171229592032224290151147774395244837867039090643593229420088951273547355221335151640596222660235972489198029588740847300183028085278249000769712164790405102238543822773365174551464534858048964688828059868487560483330691614785075383354111266899071408830450588062267486017850882009768425047881675718399695486993201874855800642644994383001813205754084561392047432141250568, 1983240293945146140033852517734200985095258198961124045721515106354476136601942913452147724068417433907799963858343126109236747462846922326827573858621892870664770577901259533960620922901825461771483901988669059534234356860785800264676617573583470816500270246796379365272272134621070586891816531801836706831975477006560174686979209217424421812048336081932145357098199153951675376952542619453614914399101917033065224798752489440959872875753380358372786530207078745364138838170538002045682545940331190951290081316, 502259895462330610142884981435801360393799631500631751176323065336956010929127000490375839578059198839222197936667755332266040187086769604262271791861714194624329174245314377298097500451150300939205290540079113850639393811075003093235114310846397419333774012649603459117822866656979791827048290409132177273390813002507617710699462390334804426785913453597113705885438889414654209846506155558128940990622664580862610186585221515982657655145445610482286043077548402237572098107549157131923224112237488519270892688, 3636313925372071457160716501352347103989631708784751578611808007830633333273997206048181105687284794162122191885636048974395230884090069378962641168924630474311389624950387818869834917297214038035108936184933706398422085313852381162782195067420592625066321003722394881752182307546844360198756163738720249681355426813331376827904567563339591071937708878706156032336241810773025056701487762275622609626123564322769312437228111818727913604755317482641019637130878371737607580988112404384073371683950978768919660610, 6623672498490214337988616925128366011282081500120004170860928882395084268160011413321223591500301879877735750762314058813141714756512554883341313734680688907270328621052454826736522126129276020123830863782687884143562331035357923854850056863281703990235049439257713387116017235967228905980277556791262804525652151995437027649779714485665581668543207811333542545522943962267017069431142840621139020717809838817680131919424573700042120424582010462728127036532619452957481856078279118954097058171060224, 15660115839098672021506709775442533705694626108858494129682823609948277739245424692997631009365837721396049444800222917264014364973334382957427228012226974415912911087978455278852037254289564705685505352205942150363459757170615363104446359412408704128473982087078044354638792199304865888657689693664218722679316507557529740176121466046789191225835520]

theorem good7 : V002.Good 7 1696 :=
  ⟨_, V002.sf_colOf (as := P1696) (N := 1696) (by decide +kernel) (by decide +kernel)⟩

/-! ### The dynamic programme is attained -/

theorem H_pos : ∀ k, 1 ≤ k → 1 ≤ H k := by
  intro k hk
  rcases Nat.lt_or_ge k 8 with hlt | hge
  · interval_cases k <;> decide
  · obtain ⟨j, rfl⟩ : ∃ j, k = j + 8 := ⟨k - 8, by omega⟩
    rw [H]
    have := le_max_left (3 * H (j + 7) + 1) (max (10 * H (j + 6) + 2) (max (33 * H (j + 5) + 6)
      (max (111 * H (j + 4) + 43) (380 * H (j + 3) + 148))))
    omega

theorem good_H : ∀ k, 1 ≤ k → V002.Good k (H k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.lt_or_ge k 8 with hlt | hge
    · interval_cases k
      · exact V002.good1
      · exact V002.good2
      · exact V002.good3
      · exact V002.good4
      · exact V002.good5
      · exact V002.good6
      · exact good7
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 8 := ⟨k - 8, by omega⟩
      have h7 := ih (j + 7) (by omega) (by omega)
      have h6 := ih (j + 6) (by omega) (by omega)
      have h5 := ih (j + 5) (by omega) (by omega)
      have h4 := ih (j + 4) (by omega) (by omega)
      have h3 := ih (j + 3) (by omega) (by omega)
      rw [H]
      exact V002.good_max (V002.step3 h7) (V002.good_max (step10 h6 (H_pos _ (by omega)))
        (V002.good_max (V002.step33 h5) (V002.good_max (V002.step111 h4) (V002.step380 h3))))

/-! ### The obligations -/

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Schur.f v := by
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [v, H]
  · obtain ⟨c, hc⟩ := good_H k hk
    exact V002.le_f_of_SF (by rw [nMin_eq]; exact hk) hc

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Schur.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.Schur.Lower.V002.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Schur.Lower.V002.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Schur.nMin SqueezeBench.Schur.Lower.V002.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.Schur.nMin) (n₀ := 7) (by decide) (by decide)

end SqueezeBench.Schur.Lower.V003
