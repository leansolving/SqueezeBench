import SqueezeBench.Problems.ExGirthFive.Records.Lower.V010.Def
import SqueezeBench.Problems.ExGirthFive.Records.Lower.V009.Proof

/-! Record V010 for ExGirthFive, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExGirthFive/Lower/V010.lean`.

V002–V009 build on the affine plane without vertical lines (`p³` edges on `2p²` vertices). The
projective plane `PG(2,p)` has `(p+1)(p²+p+1)` edges on `2(p²+p+1)` vertices, `2p² + 2p + 1` more
edges for `2p + 2` more vertices, i.e. `p + 1/2` edges per added vertex against the `p/2` of a
fresh block. Its points are the affine points `(x, y)` and one point at infinity per pencil
(`Option (ZMod p)`: the slope `a`, or `none` for the vertical pencil); its lines are `(i, b)` — the
line of pencil `i` with coordinate `b`, i.e. `y = a x + b` or `x = b` — and the line at infinity.
An affine point `q` lies on exactly one line of each pencil, `(i, coord i q)`; a point at infinity
lies on its pencil and on the line at infinity. The girth condition is the single statement
`inc_pts` (no two distinct points on two distinct lines, which is the same as no two distinct
lines through two distinct points), and the graph on `k` blocks plus a partial block is again the
pullback of a block graph along an injection, through V008's `transport_le`. -/

namespace SqueezeBench.ExGirthFive.Lower.V010

open Finset SimpleGraph SqueezeBench SqueezeBench.ExGirthFive SqueezeBench.ExGirthFive.Lower.V008

-- Points of `PG(2,p)`: affine `(x, y)`, or the point at infinity of the pencil `i`
-- (`some a`: the slope `a`; `none`: the vertical pencil).
abbrev Pt (p : ℕ) := (ZMod p × ZMod p) ⊕ Option (ZMod p)

-- Lines: `(some a, b)` is `y = a x + b`, `(none, c)` is `x = c`, `inr ()` is the line at infinity.
abbrev Ln (p : ℕ) := (Option (ZMod p) × ZMod p) ⊕ Unit

-- The second coordinate of the unique line of the pencil `i` through the affine point `q`.
def coord {p : ℕ} (i : Option (ZMod p)) (q : ZMod p × ZMod p) : ZMod p :=
  match i with
  | some a => q.2 - a * q.1
  | none => q.1

-- Incidence: an affine point is on the lines of coordinate `coord`, a point at infinity on the
-- lines of its pencil and on the line at infinity.
def inc {p : ℕ} : Pt p → Ln p → Bool
  | .inl q, .inl (i, b) => decide (coord i q = b)
  | .inl _, .inr _ => false
  | .inr i, .inl (j, _) => decide (i = j)
  | .inr _, .inr _ => true

-- Two lines of different pencils share at most one affine point.
theorem coord_inj {p : ℕ} [Fact p.Prime] {i j : Option (ZMod p)} (hij : i ≠ j)
    {q q' : ZMod p × ZMod p} (h1 : coord i q = coord i q') (h2 : coord j q = coord j q') :
    q = q' := by
  rcases i with _ | a <;> rcases j with _ | a'
  · exact absurd rfl hij
  · simp only [coord] at h1 h2
    exact Prod.ext h1 (by linear_combination h2 + a' * h1)
  · simp only [coord] at h1 h2
    exact Prod.ext h2 (by linear_combination h1 + a * h2)
  · simp only [coord] at h1 h2
    have hne : a - a' ≠ 0 := sub_ne_zero.mpr fun h => hij (by rw [h])
    have e1 : (a - a') * q.1 = (a - a') * q'.1 := by linear_combination h2 - h1
    have hx : q.1 = q'.1 := mul_left_cancel₀ hne e1
    exact Prod.ext hx (by linear_combination h1 + a * hx)

-- No 4-cycle `P L Q M`: two distinct points on two distinct lines.
theorem inc_pts {p : ℕ} [Fact p.Prime] (P Q : Pt p) (L M : Ln p) (hPQ : P ≠ Q) (hLM : L ≠ M)
    (h1 : inc P L = true) (h2 : inc Q L = true) (h3 : inc P M = true) (h4 : inc Q M = true) :
    False := by
  rcases L with ⟨i, b⟩ | _ <;> rcases M with ⟨j, c⟩ | _
  · rcases P with q | i₁ <;> rcases Q with q' | i₂
    · simp only [inc, decide_eq_true_eq] at h1 h2 h3 h4
      by_cases hij : i = j
      · subst hij
        exact hLM (by rw [h1] at h3; rw [h3])
      · exact hPQ (by rw [coord_inj hij (h1.trans h2.symm) (h3.trans h4.symm)])
    · simp only [inc, decide_eq_true_eq] at h1 h2 h3 h4
      subst h2 h4
      exact hLM (by rw [h1] at h3; rw [h3])
    · simp only [inc, decide_eq_true_eq] at h1 h2 h3 h4
      subst h1 h3
      exact hLM (by rw [h2] at h4; rw [h4])
    · simp only [inc, decide_eq_true_eq] at h1 h2 h3 h4
      exact hPQ (by rw [h1, h2])
  · rcases P with q | i₁ <;> rcases Q with q' | i₂ <;> simp only [inc, decide_eq_true_eq,
      Bool.false_eq_true] at h1 h2 h3 h4
    exact hPQ (by rw [h1, h2])
  · rcases P with q | i₁ <;> rcases Q with q' | i₂ <;> simp only [inc, decide_eq_true_eq,
      Bool.false_eq_true] at h1 h2 h3 h4
    exact hPQ (by rw [h3, h4])
  · exact hLM rfl

-- The bipartite incidence graph, `k` disjoint copies.
def sadj2 (p : ℕ) : Pt p ⊕ Ln p → Pt p ⊕ Ln p → Bool
  | .inl P, .inr L => inc P L
  | .inr L, .inl P => inc P L
  | _, _ => false

theorem sadj2_symm {p : ℕ} {s t : Pt p ⊕ Ln p} (h : sadj2 p s t = true) : sadj2 p t s = true := by
  cases s <;> cases t <;> simp_all [sadj2]

def PG2 (k p : ℕ) : SimpleGraph (Fin k × (Pt p ⊕ Ln p)) where
  Adj u v := u.1 = v.1 ∧ sadj2 p u.2 v.2 = true
  symm := ⟨by
    rintro ⟨i, u⟩ ⟨j, v⟩ ⟨h1, h2⟩
    exact ⟨h1.symm, sadj2_symm h2⟩⟩
  loopless := ⟨by
    rintro ⟨i, u⟩ ⟨-, h⟩
    cases u <;> simp [sadj2] at h⟩

-- Adjacent vertices lie on different sides.
theorem sadj2_sides {p : ℕ} {s t : Pt p ⊕ Ln p} (h : sadj2 p s t = true) :
    s.isLeft ≠ t.isLeft := by
  cases s <;> cases t <;> simp_all [sadj2]

-- The graph is bipartite between points and lines, so it has no triangle.
theorem PG2_cliqueFree (k p : ℕ) : (PG2 k p).CliqueFree 3 := by
  intro s hs
  obtain ⟨⟨i, ta⟩, ⟨j, tb⟩, ⟨l, tc⟩, hab, hac, hbc, -⟩ := is3Clique_iff.mp hs
  have e1 := sadj2_sides hab.2
  have e2 := sadj2_sides hac.2
  have e3 := sadj2_sides hbc.2
  revert e1 e2 e3
  generalize ta.isLeft = x
  generalize tb.isLeft = y
  generalize tc.isLeft = z
  cases x <;> cases y <;> cases z <;> simp

-- Transported from `inc_pts`, as in V006.
theorem PG2_noTwo (k p : ℕ) [Fact p.Prime] : NoTwoCommonNeighbours (PG2 k p) := by
  rintro ⟨i, tx⟩ ⟨j, ty⟩ ⟨a, tu⟩ ⟨b, tv⟩ hxy huv ⟨e1, f1⟩ ⟨e2, f2⟩ ⟨e3, f3⟩ ⟨e4, f4⟩
  have hij : i = j := e1.trans e2.symm
  have hab : a = b := e1.symm.trans e3
  have hx : tx ≠ ty := fun h => hxy (Prod.ext hij h)
  have hu : tu ≠ tv := fun h => huv (Prod.ext hab h)
  cases tx with
  | inl P =>
    cases tu with
    | inl _ => simp [sadj2] at f1
    | inr L =>
      cases ty with
      | inr _ => simp [sadj2] at f2
      | inl Q =>
        cases tv with
        | inl _ => simp [sadj2] at f3
        | inr M =>
          simp only [sadj2] at f1 f2 f3 f4
          exact inc_pts P Q L M (fun h => hx (by rw [h])) (fun h => hu (by rw [h])) f1 f2 f3 f4
  | inr L =>
    cases tu with
    | inr _ => simp [sadj2] at f1
    | inl P =>
      cases ty with
      | inl _ => simp [sadj2] at f2
      | inr M =>
        cases tv with
        | inr _ => simp [sadj2] at f3
        | inl Q =>
          simp only [sadj2] at f1 f2 f3 f4
          exact inc_pts P Q L M (fun h => hu (by rw [h])) (fun h => hx (by rw [h])) f1 f3 f2 f4

-- The `p + 1` lines through a point, indexed by `Option (ZMod p)`.
def lineOf {p : ℕ} : Pt p → Option (ZMod p) → Ln p
  | .inl q, t => .inl (t, coord t q)
  | .inr j, some b => .inl (j, b)
  | .inr _, none => .inr ()

theorem inc_lineOf {p : ℕ} (P : Pt p) (t : Option (ZMod p)) : inc P (lineOf P t) = true := by
  rcases P with q | j <;> rcases t with _ | b <;> simp [inc, lineOf]

theorem lineOf_inj {p : ℕ} (P : Pt p) : Function.Injective (lineOf P) := by
  rcases P with q | j <;> rintro (_ | b) (_ | b') h <;> simp_all [lineOf]

-- `k` full planes `PG(2,p)` plus a partial one: `s` pencils (their `s·p` lines and `s` points at
-- infinity), `m` affine points, and the line at infinity if `l = 1`.
theorem pg_le (p : ℕ) (hp : p.Prime) (k s m l n : ℕ) (hs : s ≤ p + 1) (hm : m ≤ p * p)
    (hl : l ≤ 1) (hn : k * N p + (m + s + s * p + l) ≤ n) :
    k * E p + (s * m + s * p + s * l) ≤ f n := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : NeZero p := ⟨hp.pos.ne'⟩
  classical
  rcases Nat.eq_zero_or_pos n with rfl | hn0
  · have hNpos : 0 < N p := by unfold N; positivity
    have hk : k = 0 := by
      rcases Nat.mul_eq_zero.mp (by omega : k * N p = 0) with hk | hN
      · exact hk
      · omega
    have hs0 : s = 0 := by omega
    have hm0 : m = 0 := by omega
    have hl0 : l = 0 := by omega
    subst hk hs0 hm0 hl0
    simp
  obtain ⟨P, -, hP⟩ := Finset.exists_subset_card_eq
    (s := (univ : Finset (ZMod p × ZMod p))) (n := m) (by simpa using hm)
  obtain ⟨A, -, hA⟩ := Finset.exists_subset_card_eq
    (s := (univ : Finset (Option (ZMod p)))) (n := s) (by simpa using hs)
  obtain ⟨Lf, -, hLf⟩ := Finset.exists_subset_card_eq
    (s := (univ : Finset Unit)) (n := l) (by simpa using hl)
  let φ : (Fin k × (Pt p ⊕ Ln p) ⊕ (P ⊕ (A ⊕ (A × ZMod p ⊕ Lf)))) →
      Fin (k + 1) × (Pt p ⊕ Ln p) := fun v =>
    match v with
    | .inl (i, w) => (i.castSucc, w)
    | .inr (.inl q) => (Fin.last k, .inl (.inl q.1))
    | .inr (.inr (.inl a)) => (Fin.last k, .inl (.inr a.1))
    | .inr (.inr (.inr (.inl (a, b)))) => (Fin.last k, .inr (.inl (a.1, b)))
    | .inr (.inr (.inr (.inr _))) => (Fin.last k, .inr (.inr ()))
  have hφ : Function.Injective φ := by
    have hne : ∀ i : Fin k, i.castSucc ≠ Fin.last k := fun i => (Fin.castSucc_lt_last i).ne
    rintro (⟨i, w⟩ | q | a | ⟨a, b⟩ | u) (⟨j, w'⟩ | q' | a' | ⟨a', b'⟩ | u') h <;>
      simp only [φ, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq, and_false,
        true_and, Fin.castSucc_inj] at h
    all_goals first
      | (obtain ⟨rfl, rfl⟩ := h; rfl)
      | exact absurd h.1 (hne _)
      | exact absurd h.1.symm (hne _)
      | (obtain ⟨ha, rfl⟩ := h; rw [Subtype.ext ha])
      | rw [Subtype.ext h]
      | rw [Subtype.ext (Subsingleton.elim u.1 u'.1)]
  let F : (Fin k × (Pt p × Option (ZMod p)) ⊕ (P × A ⊕ (A × ZMod p ⊕ A × Lf))) →
      Sym2 (Fin k × (Pt p ⊕ Ln p) ⊕ (P ⊕ (A ⊕ (A × ZMod p ⊕ Lf)))) := fun e =>
    match e with
    | .inl (i, Q, t) => s(.inl (i, .inl Q), .inl (i, .inr (lineOf Q t)))
    | .inr (.inl (q, a)) => s(.inr (.inl q), .inr (.inr (.inr (.inl (a, coord a.1 q.1)))))
    | .inr (.inr (.inl (a, b))) => s(.inr (.inr (.inl a)), .inr (.inr (.inr (.inl (a, b)))))
    | .inr (.inr (.inr (a, u))) => s(.inr (.inr (.inl a)), .inr (.inr (.inr (.inr u))))
  have hF : Function.Injective F := by
    rintro (⟨i, Q, t⟩ | ⟨q, a⟩ | ⟨a, b⟩ | ⟨a, u⟩) (⟨j, Q', t'⟩ | ⟨q', a'⟩ | ⟨a', b'⟩ | ⟨a', u'⟩) h <;>
      simp only [F, Sym2.eq_iff, Prod.mk.injEq, Sum.inl.injEq, Sum.inr.injEq, reduceCtorEq,
        and_false, false_and, or_false] at h
    · obtain ⟨⟨rfl, rfl⟩, -, ht⟩ := h
      rw [lineOf_inj _ ht]
    · obtain ⟨rfl, rfl, -⟩ := h; rfl
    · obtain ⟨rfl, -, rfl⟩ := h; rfl
    · obtain ⟨rfl, rfl⟩ := h; rfl
  have hE : ∀ e, F e ∈ ((PG2 (k + 1) p).comap φ).edgeSet := by
    rintro (⟨i, Q, t⟩ | ⟨q, a⟩ | ⟨a, b⟩ | ⟨a, u⟩)
    · simp [F, φ, PG2, sadj2, inc_lineOf]
    · simp [F, φ, PG2, sadj2, inc]
    · simp [F, φ, PG2, sadj2, inc]
    · simp [F, φ, PG2, sadj2, inc]
  have hcard : Fintype.card (Fin k × (Pt p ⊕ Ln p) ⊕ (P ⊕ (A ⊕ (A × ZMod p ⊕ Lf)))) ≤ n := by
    simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, ZMod.card,
      Fintype.card_option, Fintype.card_coe, Fintype.card_unit, hP, hA, hLf]
    refine le_of_eq_of_le ?_ hn
    unfold N
    ring
  have := transport_le ((PG2 (k + 1) p).comap φ)
    (comap_cliqueFree φ hφ _ (PG2_cliqueFree (k + 1) p))
    (comap_noTwo φ hφ _ (PG2_noTwo (k + 1) p)) hn0 hcard F hF hE
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, ZMod.card,
    Fintype.card_option, Fintype.card_coe, hP, hA, hLf] at this
  refine le_of_eq_of_le ?_ this
  unfold E
  ring

-- Each candidate of `part3` is a partial plane of `pg_le` (with `l = 1`), or `0`.
theorem candB_le (p n k r s : ℕ) (hp : p.Prime) (hs : s ≤ p + 1) (hkr : k * N p + r ≤ n) :
    k * E p + candB p r s ≤ f n := by
  unfold candB
  split_ifs with hfit
  · have hmin := min_le_left (r - 1 - s * (p + 1)) (p * p)
    have e : s * (p + 1) = s * p + s := by ring
    have := pg_le p hp k s (min (r - 1 - s * (p + 1)) (p * p)) 1 n hs (min_le_right _ _) le_rfl
      (by omega)
    refine le_of_eq_of_le ?_ this
    ring
  · have := pg_le p hp k 0 0 0 n (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) (by omega)
    simpa using this

-- Both candidates use at most `p + 1` pencils because `r < N p`.
theorem blk3_le (p n : ℕ) (hp : p.Prime) : blk3 p n ≤ f n := by
  have hp0 := hp.pos
  have hN : N p = 2 * (p * p) + 2 * p + 2 := by unfold N; ring
  have hNpos : 0 < N p := by omega
  have hr : n % N p < N p := Nat.mod_lt _ hNpos
  have hkr : n / N p * N p + n % N p ≤ n := by
    rw [mul_comm]; exact (Nat.div_add_mod n (N p)).le
  have hs : (n % N p + p) / (2 * (p + 1)) + 1 ≤ p + 1 := by
    have : (n % N p + p) / (2 * (p + 1)) < p + 1 := by
      rw [Nat.div_lt_iff_lt_mul (by omega)]
      have e : (p + 1) * (2 * (p + 1)) = 2 * (p * p) + 4 * p + 2 := by ring
      omega
    omega
  have h1 := candB_le p n (n / N p) (n % N p) ((n % N p + p) / (2 * (p + 1))) hp (by omega) hkr
  have h2 := candB_le p n (n / N p) (n % N p) ((n % N p + p) / (2 * (p + 1)) + 1) hp hs hkr
  unfold blk3 part3
  rcases le_total (candB p (n % N p) ((n % N p + p) / (2 * (p + 1))))
    (candB p (n % N p) ((n % N p + p) / (2 * (p + 1)) + 1)) with h | h
  · rw [max_eq_right h, mul_comm]; exact h2
  · rw [max_eq_left h, mul_comm]; exact h1

theorem blocks3_valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExGirthFive.f blocks3 := by
  intro n
  have h : ∀ l : List ℕ, (∀ p ∈ l, Nat.Prime p) →
      (l.map fun p => blk3 p n).foldr max 0 ≤ f n := by
    intro l hl
    induction l with
    | nil => exact Nat.zero_le _
    | cons c t ih =>
        exact max_le (blk3_le c n (hl c (by simp))) (ih fun q hq => hl q (by simp [hq]))
  exact h primes primes_prime

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExGirthFive.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.ExGirthFive.Lower.V009.valid blocks3_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExGirthFive.Lower.V009.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExGirthFive.nMin
      SqueezeBench.ExGirthFive.Lower.V009.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.ExGirthFive.nMin) (n₀ := 266)
    (by decide) (by decide +kernel)

end SqueezeBench.ExGirthFive.Lower.V010
