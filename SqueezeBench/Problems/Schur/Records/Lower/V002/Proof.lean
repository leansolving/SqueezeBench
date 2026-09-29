import SqueezeBench.Problems.Schur.Records.Lower.V002.Def
import SqueezeBench.Problems.Schur.Records.Lower.V001.Proof

/-! Record V002 for Schur, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Schur/Lower/V002.lean`.

The bound is the dynamic programme `H` of `Def.lean` over the four S-template steps
`S(k+1) ≥ 3S(k)+1`, `S(k+3) ≥ 33S(k)+6`, `S(k+4) ≥ 111S(k)+43`, `S(k+5) ≥ 380S(k)+148`
(Rowley 2021, Ageron et al. 2022), started from the explicit sum-free partitions of `[1, N]` for
`N = 1, 4, 13, 44, 160, 536, 1680`. The construction (Theorem 2.3 of Ageron et al., generalising
Abbott–Hanson) is formalised once, `sf_tmplApply`, for an abstract S-template `IsTemplate`; the
templates and partitions are lists of bitsets, and the kernel checks them with `chk`, `chkW`,
`chkBelow`, `chkCov` (`Nat.shiftLeft`, `Nat.land` are GMP-accelerated). Proofs reason; the kernel
only checks the data. -/

namespace SqueezeBench.Schur.Lower.V002

open SqueezeBench Finset

-- `c` colours `[1, N]` with colours `< k` and has no monochromatic `x + y = z` there.
def SF (k N : ℕ) (c : ℕ → ℕ) : Prop :=
  (∀ x, 1 ≤ x → x ≤ N → c x < k) ∧
    ∀ x y, 1 ≤ x → 1 ≤ y → x + y ≤ N → c x = c y → c (x + y) ≠ c x

-- `[1, N]` has a sum-free `k`-colouring.
def Good (k N : ℕ) : Prop := ∃ c, SF k N c

theorem le_f_of_SF {k N : ℕ} {c : ℕ → ℕ} (hk : nMin ≤ k) (h : SF k N c) : N ≤ f k := by
  have hk1 : 1 ≤ k := by simpa [nMin] using hk
  refine le_f hk fun M hM => ?_
  by_contra hcon
  have hMN : M ≤ N := by omega
  obtain ⟨x, hx, y, hy, z, hz, hsum, hxy, hyz⟩ :=
    hM (fun n => ⟨if c n < k then c n else 0, by split <;> omega⟩)
  rw [mem_Icc] at hx hy hz
  have hcx : c x < k := h.1 x hx.1 (by omega)
  have hcy : c y < k := h.1 y hy.1 (by omega)
  have hcz : c z < k := h.1 z hz.1 (by omega)
  have hxy' : c x = c y := by
    have := congrArg Fin.val hxy
    simpa [hcx, hcy] using this
  have hyz' : c y = c z := by
    have := congrArg Fin.val hyz
    simpa [hcy, hcz] using this
  exact h.2 x y hx.1 hy.1 (by omega) hxy' (by rw [hsum]; omega)

theorem good_mono {k N M : ℕ} (h : Good k N) (hMN : M ≤ N) : Good k M := by
  obtain ⟨c, hc⟩ := h
  exact ⟨c, fun x hx hxM => hc.1 x hx (by omega), fun x y hx hy hxy => hc.2 x y hx hy (by omega)⟩

theorem good_max {k a b : ℕ} (ha : Good k a) (hb : Good k b) : Good k (max a b) := by
  rcases max_choice a b with h | h <;> rw [h] <;> assumption

theorem good_of_sumFreeCol {k N : ℕ} {c : ℕ → ℕ} (h : V001.SumFreeCol k N c) : Good k N :=
  ⟨c, fun x _ _ => h.1 x, fun x y hx hy hxy hc hz => h.2 x y hx hy hxy ⟨hc, by rw [hz, hc]⟩⟩

/-! ### S-templates (Rowley 2021; Ageron et al. 2022) -/

-- An S-template of width `q`: colours `≤ n` on `[1, q]`, the special colour `n`; every colour
-- class is sum-free, the non-special ones also modulo `q`; no special element below `m`.
structure IsTemplate (n q m : ℕ) (c : ℕ → ℕ) : Prop where
  le : ∀ x, 1 ≤ x → x ≤ q → c x ≤ n
  sf : ∀ x y, 1 ≤ x → 1 ≤ y → x + y ≤ q → c x = c y → c (x + y) ≠ c x
  wrap : ∀ x y, 1 ≤ x → 1 ≤ y → x ≤ q → y ≤ q → q < x + y → c x = c y → c x ≠ n →
    c (x + y - q) ≠ c x
  one_le_m : 1 ≤ m
  m_le : m ≤ q
  below : ∀ x, 1 ≤ x → x < m → c x ≠ n

-- Rows of width `q`: `x = (α - 1) q + u` with `u ∈ [1, q]`; `u` keeps its template colour unless
-- it is special, in which case row `α` is coloured by `g`.
def tmplApply (c : ℕ → ℕ) (n q : ℕ) (g : ℕ → ℕ) (x : ℕ) : ℕ :=
  if c ((x - 1) % q + 1) < n then c ((x - 1) % q + 1) else n + g ((x - 1) / q + 1)

-- The row and column of `x + y` from those of `x` and `y`.
theorem row_col_add {q : ℕ} (hq : 0 < q) {x y : ℕ} (hx : 1 ≤ x) (hy : 1 ≤ y) :
    ((x - 1) % q + 1 + ((y - 1) % q + 1) ≤ q →
      (x + y - 1) % q + 1 = (x - 1) % q + 1 + ((y - 1) % q + 1) ∧
      (x + y - 1) / q = (x - 1) / q + (y - 1) / q) ∧
    (q < (x - 1) % q + 1 + ((y - 1) % q + 1) →
      (x + y - 1) % q + 1 = (x - 1) % q + 1 + ((y - 1) % q + 1) - q ∧
      (x + y - 1) / q = (x - 1) / q + (y - 1) / q + 1) := by
  have hx' := Nat.mod_add_div (x - 1) q
  have hy' := Nat.mod_add_div (y - 1) q
  have hxm := Nat.mod_lt (x - 1) hq
  have hym := Nat.mod_lt (y - 1) hq
  set a := (x - 1) % q with ha
  set b := (y - 1) % q with hb
  set α := (x - 1) / q with hα
  set β := (y - 1) / q with hβ
  have hz : x + y - 1 = (a + b + 1) + q * (α + β) := by
    rw [Nat.mul_add]; omega
  constructor
  · intro h
    have hlt : a + b + 1 < q := by omega
    rw [hz, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hq, Nat.mod_eq_of_lt hlt,
      Nat.div_eq_of_lt hlt]
    omega
  · intro h
    have hge : q ≤ a + b + 1 := by omega
    have hlt2 : a + b + 1 < 2 * q := by omega
    have hdiv : (a + b + 1) / q = 1 := by
      rw [Nat.div_eq_of_lt_le] <;> omega
    have hmod : (a + b + 1) % q = a + b + 1 - q := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    rw [hz, Nat.add_mul_mod_self_left, Nat.add_mul_div_left _ _ hq, hmod, hdiv]
    omega

-- In `[1, pq + m - 1]`, a special column forces the row to be at most `p`.
theorem row_le_of_special {n q m p : ℕ} {c : ℕ → ℕ} (ht : IsTemplate n q m c) {x : ℕ}
    (hx : 1 ≤ x) (hxN : x ≤ p * q + m - 1) (hs : ¬ c ((x - 1) % q + 1) < n) :
    (x - 1) / q + 1 ≤ p := by
  have hq : 0 < q := lt_of_lt_of_le ht.one_le_m ht.m_le
  have hmq := ht.m_le
  by_contra hcon
  have hp : p ≤ (x - 1) / q := by omega
  have h1 : p * q ≤ x - 1 := (Nat.le_div_iff_mul_le hq).mp hp
  have h2 : (x - 1) / q < p + 1 := by
    rw [Nat.div_lt_iff_lt_mul hq, Nat.add_mul, Nat.one_mul]
    omega
  have h3 : (x - 1) / q = p := by omega
  have h4 := Nat.mod_add_div (x - 1) q
  rw [h3, Nat.mul_comm] at h4
  have h5 : (x - 1) % q + 1 < m := by omega
  have hle := ht.le ((x - 1) % q + 1) (by omega) (by have := Nat.mod_lt (x - 1) hq; omega)
  exact ht.below _ (by omega) h5 (by omega)

theorem sf_tmplApply {n q m l p : ℕ} {c g : ℕ → ℕ} (ht : IsTemplate n q m c) (hg : SF l p g) :
    SF (n + l) (p * q + m - 1) (tmplApply c n q g) := by
  have hq : 0 < q := lt_of_lt_of_le ht.one_le_m ht.m_le
  have hcol : ∀ x, 1 ≤ (x - 1) % q + 1 ∧ (x - 1) % q + 1 ≤ q := fun x =>
    ⟨by omega, by have := Nat.mod_lt (x - 1) hq; omega⟩
  refine ⟨fun x hx hxN => ?_, fun x y hx hy hxy hc hz => ?_⟩
  · unfold tmplApply
    split
    · omega
    · have hrow := row_le_of_special ht hx hxN ‹_›
      have := hg.1 ((x - 1) / q + 1) (Nat.le_add_left 1 _) hrow
      omega
  · -- columns `u`, `v` and rows `α + 1`, `β + 1` of `x` and `y`
    obtain ⟨u, hu⟩ : ∃ u, u = (x - 1) % q + 1 := ⟨_, rfl⟩
    obtain ⟨v, hv⟩ : ∃ v, v = (y - 1) % q + 1 := ⟨_, rfl⟩
    obtain ⟨α, hα⟩ : ∃ α, α = (x - 1) / q := ⟨_, rfl⟩
    obtain ⟨β, hβ⟩ : ∃ β, β = (y - 1) / q := ⟨_, rfl⟩
    have hu1 : 1 ≤ u ∧ u ≤ q := hu ▸ hcol x
    have hv1 : 1 ≤ v ∧ v ≤ q := hv ▸ hcol y
    have hrc := row_col_add hq hx hy
    rw [← hu, ← hv, ← hα, ← hβ] at hrc
    have ex : tmplApply c n q g x = if c u < n then c u else n + g (α + 1) := by
      rw [tmplApply, ← hu, ← hα]
    have ey : tmplApply c n q g y = if c v < n then c v else n + g (β + 1) := by
      rw [tmplApply, ← hv, ← hβ]
    have ez : tmplApply c n q g (x + y) = if c ((x + y - 1) % q + 1) < n
        then c ((x + y - 1) % q + 1) else n + g ((x + y - 1) / q + 1) := rfl
    rw [ex, ey] at hc
    rw [ez, ex] at hz
    by_cases hcu : c u < n
    · -- non-special: `y` has the same template colour
      rw [if_pos hcu] at hc hz
      have hcv : c v = c u := by
        by_contra hne
        split_ifs at hc with hcv'
        · exact hne hc.symm
        · omega
      rcases Nat.lt_or_ge q (u + v) with hgt | hle
      · obtain ⟨hw, -⟩ := hrc.2 hgt
        rw [hw] at hz
        have := ht.wrap u v hu1.1 hv1.1 hu1.2 hv1.2 hgt hcv.symm (by omega)
        split_ifs at hz with h'
        · exact this hz
        · omega
      · obtain ⟨hw, -⟩ := hrc.1 hle
        rw [hw] at hz
        have := ht.sf u v hu1.1 hv1.1 hle hcv.symm
        split_ifs at hz with h'
        · exact this hz
        · omega
    · -- special: `y` is special too, in a row of the same `g`-colour
      rw [if_neg hcu] at hc hz
      have hcun : c u = n := by
        have := ht.le u hu1.1 hu1.2; omega
      have hcv : ¬ c v < n := by
        intro hcv'
        rw [if_pos hcv'] at hc; omega
      rw [if_neg hcv] at hc
      have hg' : g (α + 1) = g (β + 1) := by omega
      have hrx : α + 1 ≤ p := hα ▸ row_le_of_special ht hx (by omega) (hu ▸ hcu)
      have hry : β + 1 ≤ p := hβ ▸ row_le_of_special ht hy (by omega) (hv ▸ hcv)
      rcases Nat.lt_or_ge q (u + v) with hgt | hle
      · obtain ⟨hw, hr⟩ := hrc.2 hgt
        rw [hw, hr] at hz
        split_ifs at hz with h'
        · omega
        · have hrz := row_le_of_special ht (by omega : 1 ≤ x + y) hxy (by rw [hw]; exact h')
          rw [hr] at hrz
          have := hg.2 (α + 1) (β + 1) (by omega) (by omega) (by omega) hg'
          apply this
          have e : α + 1 + (β + 1) = α + β + 1 + 1 := by omega
          rw [e]; omega
      · obtain ⟨hw, -⟩ := hrc.1 hle
        rw [hw] at hz
        have hcv' : c v = n := by
          have := ht.le v hv1.1 hv1.2; omega
        have := ht.sf u v hu1.1 hv1.1 hle (by rw [hcun, hcv'])
        have hle' := ht.le (u + v) (by omega) hle
        split_ifs at hz with h'
        · omega
        · exact this (by omega)

theorem good_step {n q m : ℕ} {c : ℕ → ℕ} (ht : IsTemplate n q m c) {k N : ℕ} (h : Good k N) :
    Good (n + k) (N * q + m - 1) := by
  obtain ⟨g, hg⟩ := h
  exact ⟨_, sf_tmplApply ht hg⟩

/-! ### Bitset checks, evaluated by the kernel -/

-- `chk a N`: for every `x < N` in the set `a`, no `y ∈ a` has `x + y ∈ a`.
def chk (a : ℕ) (N : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun x r => r && (!a.testBit x || (a <<< x) &&& a == 0)) N

-- `chkW a q N`: for every `x < N` in `a`, no `y ∈ a` has `x + y - q ∈ a` when `q ≤ x + y`.
def chkW (a q : ℕ) (N : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true
    (fun x r => r && (!a.testBit x || ((a <<< x) >>> q) &&& a == 0)) N

-- `chkBelow a m`: no `x < m` lies in `a`.
def chkBelow (a : ℕ) (m : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun x r => r && !a.testBit x) m

-- `chkCov u N`: every `x` with `1 ≤ x < N` lies in `u`.
def chkCov (u : ℕ) (N : ℕ) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun x r => r && (x == 0 || u.testBit x)) N

theorem chk_spec {a N : ℕ} (h : chk a N = true) :
    ∀ x, x < N → a.testBit x = true → (a <<< x) &&& a = 0 := by
  induction N with
  | zero => intro x hx; omega
  | succ N ih =>
    have h' : (chk a N && (!a.testBit N || (a <<< N) &&& a == 0)) = true := h
    rw [Bool.and_eq_true] at h'
    intro x hx hb
    rcases Nat.lt_or_ge x N with hlt | hge
    · exact ih h'.1 x hlt hb
    · have hxN : x = N := by omega
      subst hxN
      rw [Bool.or_eq_true] at h'
      rcases h'.2 with h2 | h2
      · simp [hb] at h2
      · exact beq_iff_eq.mp h2

theorem chkW_spec {a q N : ℕ} (h : chkW a q N = true) :
    ∀ x, x < N → a.testBit x = true → ((a <<< x) >>> q) &&& a = 0 := by
  induction N with
  | zero => intro x hx; omega
  | succ N ih =>
    have h' : (chkW a q N && (!a.testBit N || ((a <<< N) >>> q) &&& a == 0)) = true := h
    rw [Bool.and_eq_true] at h'
    intro x hx hb
    rcases Nat.lt_or_ge x N with hlt | hge
    · exact ih h'.1 x hlt hb
    · have hxN : x = N := by omega
      subst hxN
      rw [Bool.or_eq_true] at h'
      rcases h'.2 with h2 | h2
      · simp [hb] at h2
      · exact beq_iff_eq.mp h2

theorem chkBelow_spec {a m : ℕ} (h : chkBelow a m = true) : ∀ x, x < m → a.testBit x = false := by
  induction m with
  | zero => intro x hx; omega
  | succ m ih =>
    have h' : (chkBelow a m && !a.testBit m) = true := h
    rw [Bool.and_eq_true] at h'
    intro x hx
    rcases Nat.lt_or_ge x m with hlt | hge
    · exact ih h'.1 x hlt
    · have hxm : x = m := by omega
      subst hxm
      simpa using h'.2

theorem chkCov_spec {u N : ℕ} (h : chkCov u N = true) :
    ∀ x, 1 ≤ x → x < N → u.testBit x = true := by
  induction N with
  | zero => intro x _ hx; omega
  | succ N ih =>
    have h' : (chkCov u N && (N == 0 || u.testBit N)) = true := h
    rw [Bool.and_eq_true] at h'
    intro x hx1 hx
    rcases Nat.lt_or_ge x N with hlt | hge
    · exact ih h'.1 x hx1 hlt
    · have hxN : x = N := by omega
      subst hxN
      rw [Bool.or_eq_true] at h'
      rcases h'.2 with h2 | h2
      · have := beq_iff_eq.mp h2; omega
      · exact h2

theorem testBit_add_of_chk {a N : ℕ} (h : chk a N = true) {x y : ℕ} (hx : x < N)
    (hbx : a.testBit x = true) (hby : a.testBit y = true) : a.testBit (x + y) = false := by
  have h0 := chk_spec h x hx hbx
  have := congrArg (fun t => t.testBit (x + y)) h0
  simp only [Nat.testBit_land, Nat.testBit_shiftLeft, Nat.zero_testBit] at this
  simpa [hby] using this

theorem testBit_wrap_of_chkW {a q N : ℕ} (h : chkW a q N = true) {x y : ℕ} (hx : x < N)
    (hbx : a.testBit x = true) (hby : a.testBit y = true) (hq : q ≤ x + y) :
    a.testBit (x + y - q) = false := by
  have h0 := chkW_spec h x hx hbx
  have := congrArg (fun t => t.testBit (x + y - q)) h0
  simp only [Nat.testBit_land, Nat.testBit_shiftRight, Nat.testBit_shiftLeft,
    Nat.zero_testBit] at this
  have e : q + (x + y - q) = x + y := by omega
  rw [e] at this
  simpa [hby] using this

/-! ### Colourings from lists of bitsets -/

-- The colour of `x`: the index of the first bitset containing it (`as.length` if none).
def colOf : List ℕ → ℕ → ℕ
  | [], _ => 0
  | a :: as, x => if a.testBit x then 0 else colOf as x + 1

def union : List ℕ → ℕ
  | [] => 0
  | a :: as => a ||| union as

theorem colOf_spec : ∀ (as : List ℕ) (x : ℕ), colOf as x < as.length →
    ∃ a, as[colOf as x]? = some a ∧ a.testBit x = true
  | [], x, h => by simp at h
  | a :: as, x, h => by
    simp only [colOf] at h ⊢
    split_ifs at h ⊢ with hb
    · exact ⟨a, rfl, hb⟩
    · simp only [List.length_cons] at h
      obtain ⟨a', ha', hb'⟩ := colOf_spec as x (by omega)
      exact ⟨a', by simpa using ha', hb'⟩

theorem testBit_union : ∀ (as : List ℕ) (x : ℕ), (union as).testBit x = true →
    ∃ a ∈ as, a.testBit x = true
  | [], x, h => by simp [union] at h
  | a :: as, x, h => by
    simp only [union, Nat.testBit_lor, Bool.or_eq_true] at h
    rcases h with h | h
    · exact ⟨a, List.mem_cons_self, h⟩
    · obtain ⟨a', ha', hb⟩ := testBit_union as x h
      exact ⟨a', List.mem_cons_of_mem _ ha', hb⟩

theorem colOf_lt : ∀ (as : List ℕ) (x : ℕ), (∃ a ∈ as, a.testBit x = true) →
    colOf as x < as.length
  | [], x, h => by simp at h
  | a :: as, x, h => by
    simp only [colOf, List.length_cons]
    split_ifs with hb
    · omega
    · obtain ⟨a', ha', hb'⟩ := h
      rcases List.mem_cons.mp ha' with rfl | ha'
      · simp [hb'] at hb
      · have := colOf_lt as x ⟨a', ha', hb'⟩; omega

-- The bitset of the colour of `x`.
theorem class_of {as : List ℕ} {x : ℕ} (hx : colOf as x < as.length) :
    ∃ a, as[colOf as x]? = some a ∧ a ∈ as ∧ a.testBit x = true := by
  obtain ⟨a, ha, hb⟩ := colOf_spec as x hx
  exact ⟨a, ha, List.mem_of_getElem? ha, hb⟩

-- An element of the same colour as `x` lies in the bitset of `x`.
theorem testBit_of_colOf_eq {as : List ℕ} {x y a : ℕ} (ha : as[colOf as x]? = some a)
    (hy : colOf as y < as.length) (hc : colOf as y = colOf as x) : a.testBit y = true := by
  obtain ⟨a', ha', hb⟩ := colOf_spec as y hy
  rw [hc, ha] at ha'
  have e := Option.some.inj ha'
  subst e
  exact hb

theorem sf_colOf {as : List ℕ} {N : ℕ} (hchk : ∀ a ∈ as, chk a (N + 1) = true)
    (hcov : chkCov (union as) (N + 1) = true) : SF as.length N (colOf as) := by
  have cov : ∀ x, 1 ≤ x → x ≤ N → colOf as x < as.length := fun x hx hxN =>
    colOf_lt as x (testBit_union as x (chkCov_spec hcov x hx (by omega)))
  refine ⟨cov, fun x y hx hy hxy hc hz => ?_⟩
  obtain ⟨a, ha, hmem, hbx⟩ := class_of (cov x hx (by omega))
  have hby := testBit_of_colOf_eq ha (cov y hy (by omega)) hc.symm
  have hbz := testBit_of_colOf_eq ha (cov (x + y) (by omega) hxy) hz
  have := testBit_add_of_chk (hchk a hmem) (by omega : x < N + 1) hbx hby
  rw [this] at hbz
  exact Bool.false_ne_true hbz

theorem isTemplate_colOf {as : List ℕ} {n q m : ℕ} (hlen : as.length = n + 1)
    (hchk : ∀ a ∈ as, chk a (q + 1) = true)
    (hwrap : ∀ a ∈ as.take n, chkW a q (q + 1) = true)
    (hbelow : ∀ a ∈ as.drop n, chkBelow a m = true)
    (hcov : chkCov (union as) (q + 1) = true) (hm : 1 ≤ m) (hmq : m ≤ q) :
    IsTemplate n q m (colOf as) := by
  have cov : ∀ x, 1 ≤ x → x ≤ q → colOf as x < as.length := fun x hx hxq =>
    colOf_lt as x (testBit_union as x (chkCov_spec hcov x hx (by omega)))
  refine ⟨fun x hx hxq => by have := cov x hx hxq; omega, ?_, ?_, hm, hmq, ?_⟩
  · intro x y hx hy hxy hc hz
    obtain ⟨a, ha, hmem, hbx⟩ := class_of (cov x hx (by omega))
    have hby := testBit_of_colOf_eq ha (cov y hy (by omega)) hc.symm
    have hbz := testBit_of_colOf_eq ha (cov (x + y) (by omega) hxy) hz
    have := testBit_add_of_chk (hchk a hmem) (by omega : x < q + 1) hbx hby
    rw [this] at hbz
    exact Bool.false_ne_true hbz
  · intro x y hx hy hxq hyq hgt hc hn hz
    obtain ⟨a, ha, -, hbx⟩ := class_of (cov x hx hxq)
    have hby := testBit_of_colOf_eq ha (cov y hy hyq) hc.symm
    have hbz := testBit_of_colOf_eq ha (cov (x + y - q) (by omega) (by omega)) hz
    have hi : colOf as x < n := by have := cov x hx hxq; omega
    have hmem : a ∈ as.take n :=
      List.mem_of_getElem? (by rw [List.getElem?_take_of_lt hi]; exact ha)
    have := testBit_wrap_of_chkW (hwrap a hmem) (by omega : x < q + 1) hbx hby (by omega)
    rw [this] at hbz
    exact Bool.false_ne_true hbz
  · intro x hx hxm hcn
    have hlt : colOf as x < as.length := by rw [hlen, hcn]; omega
    obtain ⟨a, ha, -, hbx⟩ := class_of hlt
    rw [hcn] at ha
    have hmem : a ∈ as.drop n :=
      List.mem_of_getElem? (i := 0) (by rw [List.getElem?_drop]; simpa using ha)
    have := chkBelow_spec (hbelow a hmem) x hxm
    rw [this] at hbx
    exact Bool.false_ne_true hbx

/-! ### The data: templates and partitions as lists of bitsets (bit `x` set iff `x` lies in the class)

Templates: the special class is last. `T3` is the tripling template (class `{1}`, special `{2, 3}`);
`T33`, `T111`, `T380` are from Ageron, Casteras, Pellerin, Portella, Rimmel, Tomasik, *New lower
bounds for Schur and weak Schur numbers*, arXiv:2112.03175, Appendix A (in the width-111 table the
element 49 is missing from the paper; it is placed in class 1, which the kernel check confirms).
Partitions: `P160` is Exoo 1994 (EJC 1, R8); `P536` and `P1680` are Fredricksen and Sweet 2000
(EJC 7, R32), expanded from their symmetric halves. -/

def T3 : List ℕ := [2, 12]

def T33 : List ℕ := [2299601474, 100712484, 1879055384, 12900499840]

def T111 : List ℕ := [1389345057850139429151540613501218, 671854818120961603134647913710788, 488045481087868356030581871086104, 178572850817084130631678500864, 2642872928625041156083094252421120]

def T380 : List ℕ := [1319166979487730993110712131257211814495978131190497859030071460963202685130192092326145473542030031019575764748578, 5150665952207972222452148472867865460337574363899009127989409308561779195861683620315869255642400275851191067140, 462498493693644119926953705544528981068986062491282491348928647524749498539027957679042175991113768744903542067224, 675790229228837857812229799332979606034007040815195898066657901308077021637025778283835470584437013275195694384320, 2267249916075386740977480423783676866596339536619087161662559466779048268029053387962272081719242784768, 2462644406184621708546456841169385978151874923080709236383270169264461677468264766249415239099428969703583063736320]

def P160 : List ℕ := [274166074712561339118624414120275197192977874992, 1107731239660319259086549367949694648517226152204, 31064962327939835719021941064387605559112776320, 1510040997960818505586321652531570310904054809666, 166896896852289766638277138493472768]

def P536 : List ℕ := [241009346897815929968501746981737250380542206335915535221711565906381358754828732250050968228216371228692837036034658492707795731222106470359101006928395995466018, 112583559863953127073472015552607243895119934028448529166783883254021966252317449345069829598655393767602624512232092005585506372897510418891655341911710288580612, 56682796024579060309163585427922133303524978944497370301051224328524067584004323760282414479003031185771380796138021365366568827297895912055524301014104778277896, 28173560534139865688878761505377476919434149049923285227724284466480670946553149040229197279454792773846063846227485291248915189612604774954655231997488200163344, 7911893933820064506213153598527754540660972091323613661303565915643149818901747358934798732676383153231473082880174925637538956086863494600601818000311235772992, 3530222200011590734824587702426326847687471380083329731501033390132544710543385277336860292383113605847711789839657431774501528432448898039313818234505887252608]

def P1680 : List ℕ := [53755864216097290093285568874247290753899682870361371451087984498430103404129942578980091739585803391227366262030730734306620657538587509727730285710964445396133195624662460023358079965109625635597481492786232397784053757895681993143721093817021631596574066684985967782954638383057494835113427496458889466005563327395147062753590817750564955638293839069189979804783921873819888217693914906895421541519730531597254892488549449419484198492817499714164976264127828131030792500376816464840623563326930597085186, 26875881842638715380035404927699486924054475047821021042551008463915403157684781722771479724624053094736153543656295519948980968165844431743906424237902644719914607189932228291954842693003669567032270605945449717023673958651038124628717938312784084449177339634634040653285023152291468553938332525451875661164957825867014850852932545684408331499181076840572967413399539746060947173578033826794307954273933998404129903385738470247199111307674343006115473484020780234458551774378053304173109683231580655452164, 13989170964594025707580002234491479720537861059123822027082051960511905703797385727197801747898520906034360857511165992699488471123206006294271461899658061410582057941377096397521911384930855358894767474805040020042571639430143139894399342128657584810063002703211155577142737887267781774277850633119758431293024470810101288386669973582710165962165931608278408329340638716660660363945129072770693083946781626933309636627523641164845190408296640833725664896078645158189647498590079956995432594278691425490184, 6771975005194327044902448803707796693715214194414510711087970660087716136195862968292432053354574855108878324182951063328506919754157176888377515369991383066397867140852114693215723911174687922382143172915374294138833893956205456685679481182037390604197427076012322854474530353254987498372346699082065010385190436483584820946657521891752847316994984509524497237105335107284901092854031034727587230162963843057247104682211072162623754733092689811238087704842992083557431790434534781675027117557535827298320, 3366046699840362875746298855153620809717678307839771932895349650691431414220417455981269214207185103034345803236461455400472135108112733942969253036365722597471070126878680807732912966147926562958440345008161101606818699008398152409881506009373294428229578006975081314877624121390482223819544205089819909929930252021160461919676386337205632759831514573383641290826495764706130838396825966251662736233214033555345304855748234850473620726509182111278006331187025620294559926813476019014900335499659934973984, 1889722442394995647869813474705011867869391390975695011803157870227265935107902216251895465682302276985486780596330680893744358065668847623787332371739272134604182338662361338582795672265186906352868822943705286514292408530738875863386617418454459851960551953262081904511369252312281786951561171849256204839366003013871848446203319151816940625774687512866284294451943919097793063268432120031097146808325255800420366763803787534404871764864496107774454130166159348732188076057269964561267176758938045514304, 854865392476105204650392272344796556223009009782096512919706622182335307419988145594952677133188831665160439634582028276935029119721869456771921928089214582296374825259231411552278888596146106557056899590185713234592425323108977870608346499609702642462984533969155228950521515617320811029720224123060589071425341316354739683524149186744026812553579263447113122241673986069842695944845306448136169018597359423773945699610022711431482551118617434080170057807251444825211140360474984177161690821621988270208]

theorem tmpl3 : IsTemplate 1 3 2 (colOf T3) :=
  isTemplate_colOf rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide)

theorem tmpl33 : IsTemplate 3 33 7 (colOf T33) :=
  isTemplate_colOf rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide)

theorem tmpl111 : IsTemplate 4 111 44 (colOf T111) :=
  isTemplate_colOf rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide)

theorem tmpl380 : IsTemplate 5 380 149 (colOf T380) :=
  isTemplate_colOf rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide) (by decide)

-- The four template steps: `S(k+1) ≥ 3S(k)+1`, `S(k+3) ≥ 33S(k)+6`, `S(k+4) ≥ 111S(k)+43`,
-- `S(k+5) ≥ 380S(k)+148`.
theorem step3 {k N : ℕ} (h : Good k N) : Good (k + 1) (3 * N + 1) := by
  have := good_step tmpl3 h
  rw [Nat.add_comm 1 k] at this
  have e : N * 3 + 2 - 1 = 3 * N + 1 := by omega
  rwa [e] at this

theorem step33 {k N : ℕ} (h : Good k N) : Good (k + 3) (33 * N + 6) := by
  have := good_step tmpl33 h
  rw [Nat.add_comm 3 k] at this
  have e : N * 33 + 7 - 1 = 33 * N + 6 := by omega
  rwa [e] at this

theorem step111 {k N : ℕ} (h : Good k N) : Good (k + 4) (111 * N + 43) := by
  have := good_step tmpl111 h
  rw [Nat.add_comm 4 k] at this
  have e : N * 111 + 44 - 1 = 111 * N + 43 := by omega
  rwa [e] at this

theorem step380 {k N : ℕ} (h : Good k N) : Good (k + 5) (380 * N + 148) := by
  have := good_step tmpl380 h
  rw [Nat.add_comm 5 k] at this
  have e : N * 380 + 149 - 1 = 380 * N + 148 := by omega
  rwa [e] at this

-- The base partitions.
theorem good1 : Good 1 1 :=
  ⟨fun _ => 0, fun _ _ _ => Nat.one_pos, fun x y hx hy hxy _ => by omega⟩

theorem good2 : Good 2 4 := step3 good1

theorem good3 : Good 3 13 := step3 good2

theorem good4 : Good 4 44 := good_of_sumFreeCol V001.col4_sumFree

theorem good5 : Good 5 160 :=
  ⟨_, sf_colOf (as := P160) (N := 160) (by decide +kernel) (by decide +kernel)⟩

theorem good6 : Good 6 536 :=
  ⟨_, sf_colOf (as := P536) (N := 536) (by decide +kernel) (by decide +kernel)⟩

theorem good7 : Good 7 1680 :=
  ⟨_, sf_colOf (as := P1680) (N := 1680) (by decide +kernel) (by decide +kernel)⟩

/-! ### The dynamic programme is attained -/

theorem good_H : ∀ k, 1 ≤ k → Good k (H k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases Nat.lt_or_ge k 8 with hlt | hge
    · interval_cases k
      · exact good1
      · exact good2
      · exact good3
      · exact good4
      · exact good5
      · exact good6
      · exact good7
    · obtain ⟨j, rfl⟩ : ∃ j, k = j + 8 := ⟨k - 8, by omega⟩
      have h7 := ih (j + 7) (by omega) (by omega)
      have h5 := ih (j + 5) (by omega) (by omega)
      have h4 := ih (j + 4) (by omega) (by omega)
      have h3 := ih (j + 3) (by omega) (by omega)
      rw [H]
      exact good_max (step3 h7) (good_max (step33 h5) (good_max (step111 h4) (step380 h3)))

/-! ### The obligations -/

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.Schur.f v := by
  intro k
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp [v, H]
  · obtain ⟨c, hc⟩ := good_H k hk
    exact le_f_of_SF (by rw [nMin_eq]; exact hk) hc

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Schur.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.Schur.Lower.V001.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Schur.Lower.V001.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Schur.nMin SqueezeBench.Schur.Lower.V001.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.Schur.nMin) (n₀ := 5) (by decide) (by decide)

end SqueezeBench.Schur.Lower.V002
