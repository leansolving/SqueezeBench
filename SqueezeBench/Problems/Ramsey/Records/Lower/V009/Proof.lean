import SqueezeBench.Problems.Ramsey.Records.Lower.V009.Def
import SqueezeBench.Problems.Ramsey.Records.Lower.V008.Proof

/-! Record V009 for Ramsey, lower direction, by trial claude-fable: the three obligations.
Keep the statements as written; they are copied from
`Challenges/Ramsey/Lower/V009.lean`. The record is patched at `n = 5` to `43`, the best
known lower bound on `R(5,5)` (Exoo 1989): a graph on 42 vertices with neither a clique nor
an independent set of size 5, one of the 656 such graphs listed by McKay and Radziszowski.
Its adjacency matrix is stored as a bitmask, and both colours are checked with V008's
depth-first clique checker on all 42 vertices; the graph has no useful symmetry. -/

namespace SqueezeBench.Ramsey.Lower.V009

open SqueezeBench SimpleGraph

-- The adjacency matrix of a (5,5,42)-graph: bit `42·x + y` is set iff `x ~ y`.
def mask : ℕ :=
  417992622644393043506779862260108982412131954615401482403428486126743264231165495527771948290174775135055832571740806463191061680297517862682872130641088242750013431499010608474028077963996957761240606642584403283460120350445970224112576991441796006664752729942587877245930720692414730662699476849667234887785207124383166089084822346654759735649458389344558241179044023861865080406505026414587452208177393654671711072486330090045192047308542726870728092112363312608445810605271389911887112156011519245097187400740624704847988268640

def bit (x y : ℕ) : Bool := (mask >>> (42 * min x y + max x y)) % 2 == 1

-- The graph and its complement, as relations on the naturals below 42.
def adj (x y : ℕ) : Bool := !(x == y) && bit x y

def adjc (x y : ℕ) : Bool := !(x == y) && !(bit x y)

theorem adj_k5_free : V008.cliqueFree adj 50 5 (List.range 42) = true := by decide +kernel

theorem adjc_k5_free : V008.cliqueFree adjc 50 5 (List.range 42) = true := by decide +kernel

theorem adj_symm (x y : ℕ) (h : adj x y = true) : adj y x = true := by
  simp only [adj, bit, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq] at h ⊢
  refine ⟨fun hh => h.1 hh.symm, ?_⟩
  rw [min_comm, max_comm]
  exact h.2

theorem adj_irrefl (x : ℕ) : adj x x = false := by simp [adj]

def G (N : ℕ) : SimpleGraph (Fin N) where
  Adj x y := adj x.val y.val = true
  symm := ⟨fun _ _ h => adj_symm _ _ h⟩
  loopless := ⟨fun x h => by rw [adj_irrefl] at h; exact Bool.noConfusion h⟩

theorem f5 : 43 ≤ f 5 := by
  refine le_f (by decide) ?_
  intro N hN
  by_contra hcon
  have hN42 : N ≤ 42 := by omega
  rcases hN (G N) with ⟨S, hS⟩ | ⟨T, hT⟩
  · have hcard := V008.cliqueFree_sound adj 50 5 (List.range 42) adj_k5_free
      (S.image (fun z : Fin N => z.val)) ?_ ?_
    · rw [Finset.card_image_of_injective _ Fin.val_injective, hS.card_eq] at hcard
      omega
    · intro x hx
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx
      exact List.mem_range.mpr (lt_of_lt_of_le z.isLt hN42)
    · intro x hx y hy hxy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      have hzw : z ≠ w := by rintro rfl; exact hxy rfl
      exact hS.isClique hz hw hzw
  · have hcard := V008.cliqueFree_sound adjc 50 5 (List.range 42) adjc_k5_free
      (T.image (fun z : Fin N => z.val)) ?_ ?_
    · rw [Finset.card_image_of_injective _ Fin.val_injective, hT.card_eq] at hcard
      omega
    · intro x hx
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hx
      exact List.mem_range.mpr (lt_of_lt_of_le z.isLt hN42)
    · intro x hx y hy hxy
      obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
      obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hy
      have hzw : z ≠ w := by rintro rfl; exact hxy rfl
      have hadj := hT.isClique hz hw hzw
      rw [compl_adj] at hadj
      have h2 : ¬ adj z.val w.val = true := hadj.2
      simp only [adj, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq,
        not_and] at h2
      simp only [adjc, Bool.and_eq_true, Bool.not_eq_true', beq_eq_false_iff_ne, ne_eq]
      exact ⟨hxy, (Bool.not_eq_true _).mp (h2 hxy)⟩

theorem valid : SqueezeBench.LowerBoundHolds SqueezeBench.Ramsey.f record :=
  SqueezeBench.patch_valid SqueezeBench.Ramsey.Lower.V008.valid f5

theorem improves : SqueezeBench.ImprovesLower SqueezeBench.Ramsey.Lower.V008.record record :=
  SqueezeBench.patch_improves (by decide)

theorem strict :
    SqueezeBench.StrictlyImprovesLower SqueezeBench.Ramsey.nMin SqueezeBench.Ramsey.Lower.V008.record record :=
  SqueezeBench.patch_strict (by decide) (by decide)

end SqueezeBench.Ramsey.Lower.V009
