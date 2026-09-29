import SqueezeBench.Problems.ExC4.Records.Lower.V007.Def
import SqueezeBench.Problems.ExC4.Records.Lower.V006.Proof

/-! Record V007 for ExC4, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/ExC4/Lower/V007.lean`. -/

namespace SqueezeBench.ExC4.Lower.V007

open Finset SimpleGraph SqueezeBench.ExC4 SqueezeBench.ExC4.Lower.V006

/-! ### Graphs given by a table of neighbourhood bitmasks -/

-- A graph on `Fin k` given by a list `L` of `k` neighbourhood bitmasks: `i ~ j` iff bit `j`
-- of `L[i]` and bit `i` of `L[j]` are set (symmetrised, so it is a graph for any list).
def rowOf (L : List ℕ) (i : ℕ) : ℕ := L.getD i 0

def tblGraph (L : List ℕ) : SimpleGraph (Fin L.length) where
  Adj a b := a ≠ b ∧ (rowOf L a).testBit b = true ∧ (rowOf L b).testBit a = true
  symm := ⟨fun _ _ ⟨h1, h2, h3⟩ => ⟨h1.symm, h3, h2⟩⟩
  loopless := ⟨fun _ ⟨h1, _, _⟩ => h1 rfl⟩

instance (L : List ℕ) : DecidableRel (tblGraph L).Adj :=
  fun i j => inferInstanceAs (Decidable (i ≠ j ∧ (rowOf L i).testBit j = true ∧ (rowOf L j).testBit i = true))

-- `x` has at most one bit set.
def atMostOneBit (x : ℕ) : Bool := x == 0 || x == 2 ^ x.log2

theorem eq_of_testBit_two_pow {j c : ℕ} (h : (2 ^ j).testBit c = true) : c = j := by
  by_contra hne
  rw [Nat.testBit_two_pow_of_ne (fun hj => hne hj.symm)] at h
  exact Bool.noConfusion h

theorem atMostOneBit_spec {x u v : ℕ} (h : atMostOneBit x = true) (hu : x.testBit u = true)
    (hv : x.testBit v = true) : u = v := by
  simp only [atMostOneBit, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with rfl | h
  · simp at hu
  · rw [h] at hu hv
    rw [eq_of_testBit_two_pow hu, eq_of_testBit_two_pow hv]

-- Pairwise check over all `i < j`, without indexing.
def pairsOK : List ℕ → Bool
  | [] => true
  | m :: rest => rest.all (fun m' => atMostOneBit (m &&& m')) && pairsOK rest

theorem pairsOK_spec : ∀ (L : List ℕ), pairsOK L = true →
    ∀ i j, i < j → j < L.length → atMostOneBit (rowOf L i &&& rowOf L j) = true := by
  intro L
  induction L with
  | nil => intro _ i j _ hj; simp at hj
  | cons m rest ih =>
    intro h i j hij hj
    simp only [pairsOK, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨h1, h2⟩ := h
    cases i with
    | zero =>
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [rowOf, List.getD_cons_zero, List.getD_cons_succ]
      apply h1
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp at hj; omega)]
      simp
    | succ i' =>
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      simp only [rowOf, List.getD_cons_succ]
      exact ih h2 i' j' (by omega) (by simp at hj; omega)

-- Symmetry and irreflexivity, checked with a running index: `symFrom s L` checks the rows of
-- `L` as rows `s, s+1, …`.
def rowSym (i mi : ℕ) : ℕ → List ℕ → Bool
  | _, [] => true
  | j, mj :: rest => (mi.testBit j == mj.testBit i) && rowSym i mi (j + 1) rest

def symFrom : ℕ → List ℕ → Bool
  | _, [] => true
  | i, mi :: rest => !(mi.testBit i) && rowSym i mi (i + 1) rest && symFrom (i + 1) rest

theorem rowSym_spec : ∀ (rest : List ℕ) (i mi j : ℕ), rowSym i mi j rest = true →
    ∀ b, b < rest.length → mi.testBit (j + b) = (rowOf rest b).testBit i := by
  intro rest
  induction rest with
  | nil => intro _ _ _ _ b hb; simp at hb
  | cons mj rest ih =>
    intro i mi j h b hb
    simp only [rowSym, Bool.and_eq_true, beq_iff_eq] at h
    cases b with
    | zero => simpa [rowOf] using h.1
    | succ b' =>
      simp only [rowOf, List.getD_cons_succ]
      have := ih i mi (j + 1) h.2 b' (by simp at hb; omega)
      simpa [rowOf, Nat.add_assoc, Nat.add_comm 1 b'] using this

theorem symFrom_spec : ∀ (L : List ℕ) (s : ℕ), symFrom s L = true →
    (∀ a, a < L.length → (rowOf L a).testBit (s + a) = false) ∧
    (∀ a b, a < b → b < L.length → (rowOf L a).testBit (s + b) = (rowOf L b).testBit (s + a)) := by
  intro L
  induction L with
  | nil => intro s _; exact ⟨fun a ha => by simp at ha, fun a b _ hb => by simp at hb⟩
  | cons m rest ih =>
    intro s h
    simp only [symFrom, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨h0, h1⟩, h2⟩ := h
    obtain ⟨ih1, ih2⟩ := ih (s + 1) h2
    refine ⟨fun a ha => ?_, fun a b hab hb => ?_⟩
    · cases a with
      | zero => simpa [rowOf] using h0
      | succ a' =>
        simp only [rowOf, List.getD_cons_succ]
        have := ih1 a' (by simp at ha; omega)
        simpa [rowOf, Nat.add_assoc, Nat.add_comm 1 a'] using this
    · cases a with
      | zero =>
        obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        simp only [rowOf, List.getD_cons_zero, List.getD_cons_succ]
        have := rowSym_spec rest s m (s + 1) h1 b' (by simp at hb; omega)
        simpa [rowOf, Nat.add_assoc, Nat.add_comm 1 b'] using this
      | succ a' =>
        obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
        simp only [rowOf, List.getD_cons_succ]
        have := ih2 a' b' (by omega) (by simp at hb; omega)
        simpa [rowOf, Nat.add_assoc, Nat.add_comm 1 a', Nat.add_comm 1 b'] using this

-- Popcount of the low `k` bits, and its meaning.
def popcnt : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, x => x % 2 + popcnt fuel (x / 2)

theorem popcnt_eq (k : ℕ) :
    ∀ x, popcnt k x = #((univ : Finset (Fin k)).filter (fun j : Fin k => x.testBit j.val = true)) := by
  induction k with
  | zero => intro x; simp [popcnt]
  | succ k ih =>
    intro x
    rw [popcnt, ih (x / 2), card_filter, card_filter, Fin.sum_univ_succ]
    congr 1
    · rcases Nat.mod_two_eq_zero_or_one x with h | h <;> simp [Nat.testBit_zero, h]
    · refine sum_congr rfl fun j _ => ?_
      simp [Nat.testBit_succ]

def sumRows (L : List ℕ) (k : ℕ) : ℕ → ℕ
  | 0 => 0
  | i + 1 => sumRows L k i + popcnt k (rowOf L i)

theorem sumRows_eq (L : List ℕ) (k : ℕ) : ∀ n, sumRows L k n = ∑ i ∈ range n, popcnt k (rowOf L i) := by
  intro n
  induction n with
  | zero => simp [sumRows]
  | succ n ih => rw [sumRows, ih, sum_range_succ]

def tableOK (L : List ℕ) : Bool := symFrom 0 L && pairsOK L
def tableEdges (L : List ℕ) : ℕ := sumRows L L.length L.length / 2

theorem tblGraph_free (L : List ℕ) (h : pairsOK L = true) : NoTwoCommonNeighbours (tblGraph L) := by
  intro x y u v hxy huv hxu hyu hxv hyv
  obtain ⟨-, hxu, -⟩ := hxu
  obtain ⟨-, hyu, -⟩ := hyu
  obtain ⟨-, hxv, -⟩ := hxv
  obtain ⟨-, hyv, -⟩ := hyv
  have key : ∀ a b : Fin L.length, a ≠ b → atMostOneBit (rowOf L a &&& rowOf L b) = true := by
    intro a b hab
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hab) with hlt | hlt
    · exact pairsOK_spec L h a b hlt b.isLt
    · rw [Nat.land_comm]; exact pairsOK_spec L h b a hlt a.isLt
  have hu : (rowOf L x &&& rowOf L y).testBit u = true := by rw [Nat.testBit_and, hxu, hyu]; rfl
  have hv : (rowOf L x &&& rowOf L y).testBit v = true := by rw [Nat.testBit_and, hxv, hyv]; rfl
  exact huv (Fin.ext (atMostOneBit_spec (key x y hxy) hu hv))

theorem tblGraph_degree (L : List ℕ) (h : symFrom 0 L = true) (i : Fin L.length) :
    (tblGraph L).degree i = popcnt L.length (rowOf L i) := by
  obtain ⟨h1, h2⟩ := symFrom_spec L 0 h
  rw [← card_neighborFinset_eq_degree, neighborFinset_eq_filter, popcnt_eq]
  apply congrArg Finset.card
  ext j
  simp only [mem_filter, mem_univ, true_and, tblGraph]
  constructor
  · rintro ⟨-, h, -⟩; exact h
  · intro hij
    have hne : i ≠ j := by
      rintro rfl
      have := h1 i i.isLt
      simp only [Nat.zero_add] at this
      rw [this] at hij; exact Bool.noConfusion hij
    refine ⟨hne, hij, ?_⟩
    rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hlt
    · have := h2 i j hlt j.isLt
      simp only [Nat.zero_add] at this
      rw [← this]; exact hij
    · have := h2 j i hlt i.isLt
      simp only [Nat.zero_add] at this
      rw [this]; exact hij

theorem table_bound (L : List ℕ) (h : tableOK L = true) : tableEdges L ≤ f L.length := by
  simp only [tableOK, Bool.and_eq_true] at h
  obtain ⟨hs, hp⟩ := h
  rcases Nat.eq_zero_or_pos L.length with h0 | hpos
  · simp [tableEdges, h0, sumRows]
  have hdeg := sum_degrees_eq_twice_card_edges (tblGraph L)
  have hsum : ∑ i : Fin L.length, (tblGraph L).degree i = sumRows L L.length L.length := by
    rw [sumRows_eq, Finset.sum_range]
    exact sum_congr rfl fun i _ => tblGraph_degree L hs i
  have hle := le_f_of_noTwoCommonNeighbours (G := tblGraph L) (by rw [nMin_eq]; exact hpos) (tblGraph_free L hp)
  unfold tableEdges
  omega


-- `m ≤ f k` from a table of `k` masks with `m` edges, all three facts checked by the kernel.
theorem tbl_of (L : List ℕ) (m k : ℕ) (hL : L.length = k) (hok : tableOK L = true)
    (he : tableEdges L = m) : m ≤ f k := by
  subst hL; rw [← he]; exact table_bound L hok

/-! ### The tables (Afzaly–McKay), vertices `0 … k−1`, bit `j` of entry `i` set iff `i ~ j` -/

def L8 : List ℕ := [14, 69, 131, 49, 104, 152, 18, 36]
theorem t8 : 11 ≤ f 8 := tbl_of L8 11 8 rfl (by decide +kernel) (by decide +kernel)

def L9 : List ℕ := [14, 69, 131, 49, 104, 152, 274, 292, 192]
theorem t9 : 13 ≤ f 9 := tbl_of L9 13 9 rfl (by decide +kernel) (by decide +kernel)

def L10 : List ℕ := [14, 325, 131, 49, 104, 664, 274, 548, 578, 416]
theorem t10 : 16 ≤ f 10 := tbl_of L10 16 10 rfl (by decide +kernel) (by decide +kernel)

def L11 : List ℕ := [30, 1061, 515, 337, 137, 1218, 296, 560, 584, 388, 34]
theorem t11 : 18 ≤ f 11 := tbl_of L11 18 11 rfl (by decide +kernel) (by decide +kernel)

def L12 : List ℕ := [30, 37, 2563, 337, 1161, 194, 2344, 1584, 584, 388, 2192, 1092]
theorem t12 : 21 ≤ f 12 := tbl_of L12 21 12 rfl (by decide +kernel) (by decide +kernel)

def L13 : List ℕ := [30, 4133, 2563, 337, 1161, 194, 2344, 1584, 4680, 388, 6288, 1092, 1282]
theorem t13 : 24 ≤ f 13 := tbl_of L13 24 13 rfl (by decide +kernel) (by decide +kernel)

def L14 : List ℕ := [1038, 325, 8323, 1073, 8296, 664, 4370, 4644, 2626, 2464, 6153, 9984, 1216, 2068]
theorem t14 : 27 ≤ f 14 := tbl_of L14 27 14 rfl (by decide +kernel) (by decide +kernel)

def L15 : List ℕ := [1038, 325, 8323, 1073, 8296, 664, 2322, 2596, 16962, 16800, 6153, 5312, 27648, 20500, 13056]
theorem t15 : 30 ≤ f 15 := tbl_of L15 30 15 rfl (by decide +kernel) (by decide +kernel)

def L16 : List ℕ := [1038, 33093, 8323, 1073, 8296, 33432, 2322, 2596, 16962, 16800, 6153, 5312, 60416, 20500, 13056, 4130]
theorem t16 : 33 ≤ f 16 := tbl_of L16 33 16 rfl (by decide +kernel) (by decide +kernel)

def L17 : List ℕ := [1038, 325, 73859, 1073, 69736, 664, 37138, 41508, 2626, 2464, 51209, 83712, 24656, 20612, 15360, 1216, 2068]
theorem t17 : 36 ≤ f 17 := tbl_of L17 36 17 rfl (by decide +kernel) (by decide +kernel)

def L18 : List ℕ := [132110, 325, 73859, 1073, 69736, 664, 37138, 41508, 2626, 133536, 51209, 83712, 155728, 20612, 15360, 1216, 2068, 4609]
theorem t18 : 39 ≤ f 18 := tbl_of L18 39 18 rfl (by decide +kernel) (by decide +kernel)

def L19 : List ℕ := [132110, 325, 73859, 1073, 69736, 664, 37138, 41508, 2626, 133536, 51209, 83712, 155728, 20612, 15360, 263360, 264212, 266753, 229376]
theorem t19 : 42 ≤ f 19 := tbl_of L19 42 19 rfl (by decide +kernel) (by decide +kernel)

def L20 : List ℕ := [132110, 325, 73859, 263217, 69736, 664, 37138, 41508, 264770, 133536, 51209, 83712, 155728, 282756, 15360, 525504, 526356, 528897, 532744, 491520]
theorem t20 : 46 ≤ f 20 := tbl_of L20 46 20 rfl (by decide +kernel) (by decide +kernel)

def L21 : List ℕ := [132110, 1048901, 73859, 263217, 69736, 1049240, 37138, 41508, 264770, 133536, 51209, 83712, 155728, 282756, 1063936, 525504, 526356, 528897, 532744, 1540096, 540706]
theorem t21 : 50 ≤ f 21 := tbl_of L21 50 21 rfl (by decide +kernel) (by decide +kernel)

def L22 : List ℕ := [132110, 1048901, 73859, 263217, 69736, 1049240, 2134290, 41508, 264770, 133536, 51209, 83712, 155728, 282756, 1063936, 2622656, 526356, 528897, 532744, 1540096, 540706, 32832]
theorem t22 : 52 ≤ f 22 := tbl_of L22 52 22 rfl (by decide +kernel) (by decide +kernel)

def L23 : List ℕ := [4195342, 262469, 41091, 2098225, 1056872, 66200, 20754, 528932, 2099778, 4196768, 137225, 141056, 541888, 1083412, 4296768, 2187268, 442400, 330752, 1769474, 3412096, 4988944, 557320, 1065473]
theorem t23 : 56 ≤ f 23 := tbl_of L23 56 23 rfl (by decide +kernel) (by decide +kernel)

def L24 : List ℕ := [4195342, 262469, 41091, 2098225, 9445480, 66200, 8409362, 528932, 2099778, 4196768, 137225, 141056, 541888, 1083412, 4296768, 2187268, 442400, 8719360, 1769474, 3412096, 4988944, 557320, 1065473, 131152]
theorem t24 : 59 ≤ f 24 := tbl_of L24 59 24 rfl (by decide +kernel) (by decide +kernel)

def L25 : List ℕ := [4195342, 262469, 41091, 2098225, 9445480, 66200, 8409362, 528932, 2099778, 4196768, 137225, 141056, 541888, 1083412, 4296768, 2187268, 442400, 25496576, 1769474, 3412096, 4988944, 17334536, 17842689, 16908368, 14811136]
theorem t25 : 63 ≤ f 25 := tbl_of L25 63 25 rfl (by decide +kernel) (by decide +kernel)

def L26 : List ℕ := [33555470, 2130245, 139395, 5243953, 73832, 33432, 67858, 16910884, 4211266, 541088, 530441, 16782528, 322560, 8409108, 34616064, 2363426, 34472016, 1376388, 4427776, 10552832, 2244616, 9994242, 25428232, 23601152, 46139520, 16859137]
theorem t26 : 67 ≤ f 26 := tbl_of L26 67 26 rfl (by decide +kernel) (by decide +kernel)

def L27 : List ℕ := [8389646, 4194629, 172163, 66609, 17834088, 262808, 16795922, 2230820, 528962, 33558944, 101189641, 69223616, 75571968, 68194324, 362560, 33841156, 4345864, 17367172, 8962080, 1443072, 6823952, 13633664, 36765698, 19140609, 42074192, 21005824, 15360]
theorem t27 : 71 ≤ f 27 := tbl_of L27 71 27 rfl (by decide +kernel) (by decide +kernel)

def L28 : List ℕ := [263182, 18874693, 67248259, 134251569, 532584, 6292120, 34081042, 67176996, 49730, 1065376, 1054729, 33625280, 10513408, 151572, 134492928, 8585480, 17074304, 38838276, 4800513, 76808272, 17434112, 29364258, 36044832, 69767168, 137428994, 138545216, 143130756, 117456904]
theorem t28 : 76 ≤ f 28 := tbl_of L28 76 28 rfl (by decide +kernel) (by decide +kernel)

def L29 : List ℕ := [263182, 18874693, 67248259, 134251569, 268968040, 6292120, 34081042, 67176996, 49730, 1065376, 1054729, 33625280, 10513408, 268587028, 134492928, 8585480, 285509760, 38838276, 4800513, 76808272, 17434112, 29364258, 36044832, 69767168, 405864450, 138545216, 143130756, 117456904, 16850960]
theorem t29 : 80 ≤ f 29 := tbl_of L29 80 29 rfl (by decide +kernel) (by decide +kernel)

def L30 : List ℕ := [537134094, 18874693, 67248259, 134251569, 268968040, 6292120, 34081042, 67176996, 49730, 537936288, 1054729, 33625280, 10513408, 268587028, 134492928, 8585480, 285509760, 38838276, 4800513, 76808272, 17434112, 29364258, 36044832, 606638080, 405864450, 675416128, 143130756, 117456904, 553721872, 310379009]
theorem t30 : 85 ≤ f 30 := tbl_of L30 85 30 rfl (by decide +kernel) (by decide +kernel)

def L31 : List ℕ := [537134094, 18874693, 67248259, 134251569, 268968040, 6292120, 34081042, 67176996, 1073791554, 537936288, 1074796553, 33625280, 10513408, 268587028, 134492928, 8585480, 285509760, 38838276, 4800513, 76808272, 17434112, 29364258, 1109786656, 606638080, 405864450, 675416128, 1216872580, 117456904, 1627463696, 310379009, 339739904]
theorem t31 : 90 ≤ f 31 := tbl_of L31 90 31 rfl (by decide +kernel) (by decide +kernel)

def L32 : List ℕ := [537134094, 18874693, 67248259, 2281735217, 268968040, 6292120, 34081042, 67176996, 1073791554, 537936288, 1074796553, 33625280, 10513408, 268587028, 134492928, 2156069128, 285509760, 38838276, 4800513, 76808272, 17434112, 29364258, 1109786656, 606638080, 405864450, 675416128, 1216872580, 117456904, 1627463696, 310379009, 339739904, 32776]
theorem t32 : 92 ≤ f 32 := tbl_of L32 92 32 rfl (by decide +kernel) (by decide +kernel)

def L33 : List ℕ := [269484062, 12325, 33688067, 2214592849, 16843913, 8659138, 1082132776, 263728, 545352, 4299178372, 134256784, 1073906756, 539493634, 67223586, 402727680, 72363008, 19030032, 2149910532, 2149187744, 51646720, 273448961, 549654528, 4306534912, 174063712, 5402853392, 227016708, 2717949960, 310395904, 1745895425, 1411387392, 5117052992, 4362469384, 3242197504]
theorem t33 : 96 ≤ f 33 := tbl_of L33 96 33 rfl (by decide +kernel) (by decide +kernel)

def L34 : List ℕ := [4326414, 4328522053, 1073815683, 537920561, 268505192, 100663960, 8425746, 303652, 135268930, 2151680416, 8589985801, 608000, 2147639376, 3166340, 50347008, 8598586560, 1342703636, 202117121, 554336384, 4297525248, 673194248, 4309131264, 295698945, 1147174976, 843333632, 4378869794, 1250033696, 8926658816, 8745189392, 3239313416, 2759917572, 14495519232, 10773594114, 6845137920]
theorem t34 : 102 ≤ f 34 := tbl_of L34 102 34 rfl (by decide +kernel) (by decide +kernel)

def L35 : List ℕ := [4326414, 4328522053, 1073815683, 537920561, 268505192, 100663960, 8425746, 303652, 135268930, 2151680416, 8589985801, 608000, 2147639376, 3166340, 50347008, 25778455744, 18522572820, 202117121, 554336384, 4297525248, 17853063432, 4309131264, 295698945, 1147174976, 843333632, 21558738978, 1250033696, 8926658816, 8745189392, 3239313416, 2759917572, 14495519232, 10773594114, 6845137920, 34701312]
theorem t35 : 106 ≤ f 35 := tbl_of L35 106 35 rfl (by decide +kernel) (by decide +kernel)

def L36 : List ℕ := [917518, 4295000389, 671089283, 2147615793, 34527512680, 8598331544, 269486354, 1090527780, 21038146, 34362889348, 2147554056, 1074286672, 8657063424, 376992, 4372480, 4330643458, 17314358528, 17185128457, 34695880705, 1084491777, 17450533440, 43549184, 34921922816, 9133621280, 1178599808, 220233744, 8908967936, 17750360084, 2752774208, 2562719748, 6459754624, 6174016520, 63350800386, 21550338080, 13020364800, 4299424272]
theorem t36 : 110 ≤ f 36 := tbl_of L36 110 36 rfl (by decide +kernel) (by decide +kernel)

def L37 : List ℕ := [68723803150, 2181038405, 1073815683, 537920561, 268505192, 100663960, 8425746, 303652, 135268930, 42953869728, 4295018505, 608000, 34359894096, 3166340, 50347008, 21483488448, 18522572820, 34561855489, 554336384, 2150041600, 17853063432, 2161647616, 69015175681, 1147174976, 843333632, 19411255330, 1250033696, 4631691520, 4450222096, 9681764360, 9202368516, 12921077762, 11140105216, 42412802560, 103113916416, 25769939456, 17184063489]
theorem t37 : 113 ≤ f 37 := tbl_of L37 113 37 rfl (by decide +kernel) (by decide +kernel)

def L38 : List ℕ := [269484062, 38654717989, 137472641539, 2214592849, 16843913, 8659138, 18262001960, 8590198320, 545352, 8594145668, 68853733520, 1073906756, 69258970370, 67223586, 402727680, 72363008, 17198899216, 2149910532, 2149187744, 51646720, 17453318145, 549654528, 4306534912, 174063712, 5402853392, 137665970180, 11307884552, 34670134272, 1745895425, 10001321984, 5117052992, 73081946120, 37601935362, 52143587968, 249109217344, 30198988802, 156766311424, 85932900356]
theorem t38 : 117 ≤ f 38 := tbl_of L38 117 38 rfl (by decide +kernel) (by decide +kernel)

def L39 : List ℕ := [21541946382, 4325701, 2181050499, 274888393777, 805310568, 137439085208, 68987961618, 2148565540, 8598850114, 17314089376, 1073825801, 1074013952, 537468948, 68721842180, 167871552, 4296294592, 34360415232, 34381037602, 279189825536, 412385087744, 73957504, 68733116424, 1748107266, 8642363656, 377880576, 137598353412, 17466654721, 292632412672, 3305111632, 13023318032, 139859069952, 319169757316, 146566053889, 41347449088, 103280542209, 96636960768, 188980666432, 74122264608, 2282487816]
theorem t39 : 122 ≤ f 39 := tbl_of L39 122 39 rfl (by decide +kernel) (by decide +kernel)

def L40 : List ℕ := [21541946382, 4325701, 2181050499, 274888393777, 805310568, 137439085208, 68987961618, 2148565540, 8598850114, 567069903264, 1073825801, 1074013952, 537468948, 68721842180, 167871552, 4296294592, 584116229120, 34381037602, 279189825536, 412385087744, 73957504, 618488930312, 1748107266, 8642363656, 377880576, 137598353412, 17466654721, 292632412672, 553060925520, 13023318032, 139859069952, 319169757316, 696321867777, 41347449088, 103280542209, 96636960768, 188980666432, 74122264608, 2282487816, 4565565952]
theorem t40 : 127 ≤ f 40 := tbl_of L40 127 40 rfl (by decide +kernel) (by decide +kernel)

def L41 : List ℕ := [21541946382, 4325701, 2181050499, 274888393777, 805310568, 1236950712984, 68987961618, 2148565540, 8598850114, 567069903264, 1073825801, 1074013952, 537468948, 1168233469956, 1099679499328, 4296294592, 584116229120, 34381037602, 279189825536, 412385087744, 73957504, 618488930312, 1748107266, 8642363656, 377880576, 137598353412, 1116978282497, 292632412672, 553060925520, 13023318032, 139859069952, 319169757316, 696321867777, 1140859076864, 103280542209, 96636960768, 188980666432, 74122264608, 2282487816, 4565565952, 8657068064]
theorem t41 : 132 ≤ f 41 := tbl_of L41 132 41 rfl (by decide +kernel) (by decide +kernel)

def L42 : List ℕ := [21541946382, 4325701, 2181050499, 274888393777, 805310568, 2336462340760, 68987961618, 2148565540, 8598850114, 567069903264, 1073825801, 1074013952, 1100049096724, 2267745097732, 2199191127104, 1103807922368, 584116229120, 34381037602, 279189825536, 412385087744, 73957504, 618488930312, 1748107266, 1108153991432, 377880576, 137598353412, 2216489910273, 292632412672, 553060925520, 13023318032, 1239370697728, 319169757316, 696321867777, 2240370704640, 1202792169985, 96636960768, 188980666432, 74122264608, 2282487816, 4565565952, 18262036480, 8657068064]
theorem t42 : 137 ≤ f 42 := tbl_of L42 137 42 rfl (by decide +kernel) (by decide +kernel)

def L43 : List ℕ := [21541946382, 4398050836805, 2181050499, 274888393777, 805310568, 2336462340760, 68987961618, 2148565540, 8598850114, 567069903264, 1073825801, 1074013952, 1100049096724, 2267745097732, 2199191127104, 1103807922368, 584116229120, 34381037602, 279189825536, 412385087744, 73957504, 618488930312, 1748107266, 1108153991432, 377880576, 137598353412, 2216489910273, 292632412672, 553060925520, 13023318032, 1239370697728, 319169757316, 696321867777, 2240370704640, 1202792169985, 96636960768, 188980666432, 74122264608, 4400328998920, 4402612077056, 4416308547584, 4406703579168, 4123168604162]
theorem t43 : 142 ≤ f 43 := tbl_of L43 142 43 rfl (by decide +kernel) (by decide +kernel)

def L44 : List ℕ := [34628177950, 2199025434661, 137573435907, 550830080337, 4406670131337, 2686452930, 1099511922984, 274912511536, 73022849608, 8800389040516, 154627223712, 1100049162756, 8796428608513, 8590482432, 68769882370, 274945478720, 18254839810, 4398591870992, 146049892420, 275957950472, 550028509824, 4402413305890, 297533440, 2199161799936, 8831027658752, 1099729748112, 554220687360, 3330277380, 1170383835137, 586279946272, 8815555182600, 79322677280, 60198748928, 2205465976848, 1276679095296, 296906391553, 4812779307264, 5033701934084, 2302103027840, 2337067237384, 2216505116736, 10728836694018, 9002253680656, 6598160290304]
theorem t44 : 148 ≤ f 44 := tbl_of L44 148 44 rfl (by decide +kernel) (by decide +kernel)

def L45 : List ℕ := [34628177950, 2199025434661, 137573435907, 550830080337, 4406670131337, 2686452930, 18691697967400, 274912511536, 73022849608, 8800389040516, 154627223712, 1100049162756, 8796428608513, 17600776526848, 68769882370, 274945478720, 18254839810, 4398591870992, 146049892420, 275957950472, 18142214554240, 4402413305890, 297533440, 2199161799936, 8831027658752, 1099729748112, 554220687360, 17595516321796, 1170383835137, 586279946272, 8815555182600, 79322677280, 60198748928, 2205465976848, 1276679095296, 17889092435969, 4812779307264, 5033701934084, 2302103027840, 2337067237384, 2216505116736, 10728836694018, 26594439725072, 6598160290304, 4432541524032]
theorem t45 : 154 ≤ f 45 := tbl_of L45 154 45 rfl (by decide +kernel) (by decide +kernel)

def L46 : List ℕ := [34628177950, 2199025434661, 137573435907, 35735202169169, 4406670131337, 2686452930, 18691697967400, 274912511536, 73022849608, 8800389040516, 35338999312544, 1100049162756, 8796428608513, 17600776526848, 68769882370, 274945478720, 18254839810, 4398591870992, 146049892420, 275957950472, 18142214554240, 4402413305890, 297533440, 2199161799936, 44015399747584, 1099729748112, 554220687360, 17595516321796, 1170383835137, 586279946272, 8815555182600, 79322677280, 60198748928, 2205465976848, 1276679095296, 17889092435969, 4812779307264, 5033701934084, 2302103027840, 2337067237384, 2216505116736, 10728836694018, 26594439725072, 6598160290304, 4432541524032, 16778248]
theorem t46 : 157 ≤ f 46 := tbl_of L46 157 46 rfl (by decide +kernel) (by decide +kernel)

def L47 : List ℕ := [70368753615886, 17592756470085, 8796227768451, 4398063289393, 345744937064, 35184913154712, 549757978898, 137573173796, 2207613239874, 2220499403168, 1151051401225, 1100587476160, 292058325012, 4399154092032, 35184447631616, 139855021312, 70368945897552, 17592191124480, 8796127830528, 2199046459396, 275157090817, 35184658876480, 559965405216, 618547658753, 141837205512, 241072087042, 1103966060544, 4441331794052, 4400868261888, 1099817812002, 70383780767744, 8870449676304, 17612671025664, 310449799424, 588410525184, 35279029142528, 2235572420624, 71193428263040, 18837727612944, 13348770938944, 11270598167552, 75935022318336, 20341367775240, 36835787276292, 39861591605250, 96791385096224, 37521908105217]
theorem t47 : 163 ≤ f 47 := tbl_of L47 163 47 rfl (by decide +kernel) (by decide +kernel)

def L48 : List ℕ := [70368753615886, 17592756470085, 8796227768451, 145135551644721, 345744937064, 35184913154712, 549757978898, 137573173796, 142945101595202, 2220499403168, 1151051401225, 1100587476160, 292058325012, 4399154092032, 35184447631616, 139855021312, 70368945897552, 17592191124480, 8796127830528, 2199046459396, 275157090817, 35184658876480, 559965405216, 618547658753, 140879325560840, 241072087042, 1103966060544, 4441331794052, 4400868261888, 1099817812002, 70383780767744, 8870449676304, 17612671025664, 141047938154752, 588410525184, 35279029142528, 2235572420624, 71193428263040, 18837727612944, 13348770938944, 11270598167552, 75935022318336, 20341367775240, 177573275631620, 39861591605250, 96791385096224, 37521908105217, 8804699734280]
theorem t48 : 168 ≤ f 48 := tbl_of L48 168 48 rfl (by decide +kernel) (by decide +kernel)

def L49 : List ℕ := [137448391694, 35184942514501, 8796227768451, 17594350306353, 72636486979688, 140738029421208, 4297132306, 4399254473252, 299342040711746, 300649021856, 1108101728265, 5531919983808, 70927090475028, 36541061120, 140737563898112, 70061802752, 137640673360, 35184377168896, 8796127830528, 274901110788, 70369023361537, 140737775142976, 281514177331232, 6601437102081, 17610542940168, 2200650915842, 1116850962432, 281477459804292, 621297041408, 1649573625890, 70510528462976, 35463947624456, 8807916765248, 571230656000, 35296125125120, 281698319214592, 11046924353552, 141597555621889, 3438121845504, 22137066754048, 79440319089664, 4741685837840, 55525345593472, 159502200733700, 295218888835336, 215523606528002, 317759935221776, 44117906178080, 87995428372736]
theorem t49 : 174 ≤ f 49 := tbl_of L49 174 49 rfl (by decide +kernel) (by decide +kernel)

theorem tbl_le (n : ℕ) : tbl n ≤ f n := by
  unfold tbl
  split
  · exact t8
  · exact t9
  · exact t10
  · exact t11
  · exact t12
  · exact t13
  · exact t14
  · exact t15
  · exact t16
  · exact t17
  · exact t18
  · exact t19
  · exact t20
  · exact t21
  · exact t22
  · exact t23
  · exact t24
  · exact t25
  · exact t26
  · exact t27
  · exact t28
  · exact t29
  · exact t30
  · exact t31
  · exact t32
  · exact t33
  · exact t34
  · exact t35
  · exact t36
  · exact t37
  · exact t38
  · exact t39
  · exact t40
  · exact t41
  · exact t42
  · exact t43
  · exact t44
  · exact t45
  · exact t46
  · exact t47
  · exact t48
  · exact t49
  · exact Nat.zero_le _

/-! ### Bridges -/

-- A bridge between two `C₄`-free graphs creates no `C₄`.
theorem noTwo_sum_bridge {V W : Type*} {G : SimpleGraph V} {H : SimpleGraph W}
    (hG : NoTwoCommonNeighbours G) (hH : NoTwoCommonNeighbours H) (s : V) (t : W) :
    NoTwoCommonNeighbours ((G ⊕g H) ⊔ edge (Sum.inl s) (Sum.inr t)) := by
  rintro (x | x) (y | y) (u | u) (w | w) hxy huw hxu hyu hxw hyw <;>
    simp only [sup_adj, sum_adj, edge_adj, ne_eq, Sum.inl.injEq, Sum.inr.injEq,
      reduceCtorEq, false_and, and_false, or_false, false_or, and_true, not_false_eq_true,
      or_self] at hxy huw hxu hyu hxw hyw
  all_goals try simp_all
  · exact hG x y u w (fun h => hxy (by rw [h])) (fun h => huw (by rw [h])) hxu hyu hxw hyw
  · exact hH x y u w (fun h => hxy (by rw [h])) (fun h => huw (by rw [h])) hxu hyu hxw hyw

theorem f_bridge (a b : ℕ) (ha : 1 ≤ a) (hb : 1 ≤ b) : f a + f b + 1 ≤ f (a + b) := by
  obtain ⟨G, iG, hG, hGe⟩ := exists_graph a ha
  obtain ⟨H, iH, hH, hHe⟩ := exists_graph b hb
  let s : Fin a := ⟨0, ha⟩
  let t : Fin b := ⟨0, hb⟩
  let K : SimpleGraph (Fin a ⊕ Fin b) := (G ⊕g H) ⊔ edge (Sum.inl s) (Sum.inr t)
  let e : Fin a ⊕ Fin b ↪ Fin (a + b) := finSumFinEquiv.toEmbedding
  have hfree : NoTwoCommonNeighbours (K.map e) := noTwo_map e (noTwo_sum_bridge hG hH s t)
  have h1 : #(K.map e).edgeFinset = #K.edgeFinset := by convert card_edgeFinset_map e K
  have h2 : #K.edgeFinset = #(G ⊕g H).edgeFinset + 1 := by
    apply card_edgeFinset_sup_edge
    · simp [sum_adj]
    · simp
  have h3 := card_edgeFinset_sum_ge G H
  have h4 := le_f_of_noTwoCommonNeighbours (G := K.map e) (by rw [nMin_eq]; omega) hfree
  omega


/-! ### Validity of the record -/

theorem anchorLoop_le {n : ℕ} (hn : 1 ≤ n) : ∀ fuel a, n < a → anchorLoop n fuel a ≤ f n := by
  intro fuel
  induction fuel with
  | zero => intro a _; simp [anchorLoop]
  | succ fuel ih =>
    intro a ha
    simp only [anchorLoop]
    refine max_le ?_ (ih (a + 1) (by omega))
    have := delChain_le (a - n) a (tbl a) (by omega) (tbl_le a)
    rwa [Nat.sub_sub_self (le_of_lt ha)] at this

theorem anchorBest_le {n : ℕ} (hn : 1 ≤ n) : anchorBest n ≤ f n :=
  max_le (tbl_le n) (anchorLoop_le hn _ _ (by omega))

theorem anchorBest_zero : anchorBest 0 = 0 := by decide +kernel

theorem small_zero : small 0 = 0 := by decide +kernel

theorem small_le (r : ℕ) : small r ≤ f r := by
  rcases Nat.eq_zero_or_pos r with rfl | hr
  · exact max_le (SqueezeBench.ExC4.Lower.V006.valid 0)
      (by rw [anchorBest_zero]; exact Nat.zero_le _)
  · exact max_le (SqueezeBench.ExC4.Lower.V006.valid r) (anchorBest_le hr)

theorem blocks_bridge_le {q : ℕ} (hq : E q ≤ f (N q)) :
    ∀ k, 1 ≤ k → k * E q + (k - 1) ≤ f (N q * k) := by
  intro k hk
  induction k with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with rfl | hkpos
    · simpa using hq
    have hN : 0 < N q := by simp [N]
    have h1 := ih hkpos
    have h2 := f_bridge (N q * k) (N q) (Nat.mul_pos hN hkpos) hN
    have h3 : (k + 1) * E q + (k + 1 - 1) = (k * E q + (k - 1)) + E q + 1 := by
      rw [Nat.add_mul, Nat.one_mul]; omega
    rw [h3, Nat.mul_succ]
    omega

theorem blockVal_le {q n : ℕ} (hq : isPrimePowB q = true) : blockVal q n ≤ f n := by
  unfold blockVal
  split_ifs with h hr
  · have hk : 1 ≤ n / N q := Nat.div_pos h (by simp [N])
    have h1 := blocks_bridge_le (E_le hq) (n / N q) hk
    have h2 := Nat.div_add_mod n (N q)
    rw [hr, Nat.add_zero] at h2
    rw [h2] at h1
    rw [hr, small_zero]
    omega
  · have hk : 1 ≤ n / N q := Nat.div_pos h (by simp [N])
    have h1 := blocks_bridge_le (E_le hq) (n / N q) hk
    have h2 := small_le (n % N q)
    have h3 := f_bridge (N q * (n / N q)) (n % N q) (Nat.mul_pos (by simp [N]) hk) (by omega)
    rw [Nat.div_add_mod] at h3
    omega
  · exact Nat.zero_le _

theorem blockLoop_le (n : ℕ) : ∀ fuel q, blockLoop n fuel q ≤ f n := by
  intro fuel
  induction fuel with
  | zero => intro q; simp [blockLoop]
  | succ fuel ih =>
    intro q
    simp only [blockLoop]
    by_cases h1 : q * q ≤ n
    · rw [if_pos h1]
      refine max_le ?_ (ih (q + 1))
      by_cases h2 : isPrimePowB q = true
      · rw [if_pos h2]; exact blockVal_le h2
      · rw [if_neg h2]; exact Nat.zero_le _
    · rw [if_neg h1]; exact Nat.zero_le _

theorem v_valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExC4.f v :=
  SqueezeBench.pin_lowerBoundHolds fun n hn =>
    max_le (anchorBest_le (by rw [nMin_eq] at hn; exact hn)) (blockLoop_le n n 2)

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.ExC4.f record :=
  SqueezeBench.maxWith_valid SqueezeBench.ExC4.Lower.V006.valid v_valid

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.ExC4.Lower.V006.record record :=
  SqueezeBench.maxWith_improves

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.ExC4.nMin SqueezeBench.ExC4.Lower.V006.record record :=
  SqueezeBench.maxWith_strict (nMin := SqueezeBench.ExC4.nMin) (n₀ := 40) (by decide)
    (by decide +kernel)

end SqueezeBench.ExC4.Lower.V007
