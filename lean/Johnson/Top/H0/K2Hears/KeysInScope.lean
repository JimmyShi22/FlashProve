-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Top/H0/K2Hears/KeysInScope.lean: the code switch: THE FOUR FACTS ON THE PLAN's NUMBERS under
which every column that the kind's text is shown is the oracles' own (`colsOf_first`,
ColsAtStageFirst.lean), IN THE GOALS' SCOPE, at every piece of the first chain's row that holds a
switch. Statements and proofs; no definition.

The four, at a piece q with the stretch [d₁, d₂] and the place's numbers p, at the frame
⟨a, allOf (D.at a'), (D.at a').key₁, 0⟩:
  ft     the frame's number ft is p.firstTree
  first  each tree below q.base is the first of all the file's trees with its key
  low    the numbers in p.read are below 2 ^ 16
  old    the stretch's data open trees below q.base alone

  `read_opens`     where the stretch goes along the switch's declared rounds, the trees that its
                   second round opens are the numbers in p.read
  `names_along`    and its two rounds bear the names "SEND seed" and "LOC"
  `low_of_old`     so "low" follows from "old" and q.base ≤ 83
  `keys_in_scope`  THE STATEMENT: first · low · old, and q.base ≤ 83
Premises of `keys_in_scope`: the scope · the proof file's value is laid, with the data D · the row
tiles D's first chain from the base 0 (three fields of the rule of composition's `Three.Fits`) · q
is a piece of the row · its stretch is [d₁, d₂] and goes along the switch's declared rounds at p
(`Along (RoundIs (numAt t₁ t₂ 0))`: Johnson/Desc/Sound/Stretch.lean's `stretchOfData` has that of
every piece). "ft" is FtAtPub.lean's `P1K2.ft_of_pub`, beside.
Limits. At the full size alone. Nothing says that a rule of composition's row is of this form at the
proof file's description. No soundness is claimed.

-/
import Johnson.Top.H0.K2Hears.SwitchOpensEarlierTreesAtWritten
import Johnson.Desc.Sound.Stretch
import Johnson.Top.H0.Tw.K2C.Kind

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Maker
open VerifiableInference.Desc (numAt)
open VerifiableInference.Desc.Sound (Frame Piece Tiled rowData nTrees allOf Along RoundIs)
open _root_.Run.PQ (CK)
open LPFD.Full (proofDataAndDecisionOfPublicFiles RunPF)

/-- The trees that the stretch's second round opens are the numbers in "read". -/
theorem read_opens (p : P2) {t₁ t₂ : Nat} {d₁ d₂ : RDT}
    (h : Along (RoundIs (numAt t₁ t₂ 0)) (rounds p) [d₁, d₂]) : d₂.opens = p.read.map (·.1) := by
  have h2 : RoundIs (numAt t₁ t₂ 0) _ d₂ := h.2.1
  rw [h2.2.2.2.2.1, List.map_map]
  refine List.map_congr_left fun r _ => ?_
  show numAt t₁ t₂ 0 (.own r.1) = r.1
  unfold numAt
  simp

/-- The stretch's two rounds bear the switch's two names. -/
theorem names_along (p : P2) {num : Fmt.TreeSource → Nat} {d₁ d₂ : RDT}
    (h : Along (RoundIs num) (rounds p) [d₁, d₂]) :
    d₁.entry.name = "SEND seed" ∧ d₂.entry.name = "LOC" := by
  have h1 : RoundIs num _ d₁ := h.1
  have h2 : RoundIs num _ d₂ := h.2.1
  exact ⟨by rw [h1.1], by rw [h2.1]⟩

/-- "low" from "old". -/
theorem low_of_old (p : P2) {t₁ t₂ base : Nat} {d₁ d₂ : RDT}
    (h : Along (RoundIs (numAt t₁ t₂ 0)) (rounds p) [d₁, d₂])
    (hO : ∀ d ∈ [d₁, d₂], ∀ j ∈ d.opens, j < base) (hb : base ≤ 83) :
    ∀ x ∈ p.read, x.1 < 2 ^ 16 := by
  intro x hx
  have hm : x.1 ∈ d₂.opens := by
    rw [read_opens p h]
    exact List.mem_map.2 ⟨x, hx, rfl⟩
  exact low_in_scope hb (hO d₂ (by simp) x.1 hm)

variable {C : CK} {F : Frame} {S Cl W : Type}

/-- **The facts on the plan's numbers, in the goals' scope, at a piece that holds a switch.** -/
theorem keys_in_scope {o : ProofFile.SecondHashFunctionArgument} {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : RunPF}
    (hZ : VerifierAndGoals.InScope Z = true) (h : proofDataAndDecisionOfPublicFiles o Z.pol Z.lay Z.KL = .ok (D, r))
    (p₀ : Piece C F S Cl W) (l : List (Piece C F S Cl W)) (ht : Tiled p₀ l) (hb : p₀.base = 0)
    (hd : rowData p₀ l = D.ds₁) {k : Nat} {q : Piece C F S Cl W} (hq : (p₀ :: l)[k]? = some q)
    (p : P2) {t₁ t₂ : Nat} {d₁ d₂ : RDT} (hds : q.ds = [d₁, d₂])
    (hA : Along (RoundIs (numAt t₁ t₂ 0)) (rounds p) [d₁, d₂]) (a' a : Nat) :
    (∀ j, j < (⟨a, q.base, allOf (D.at a'), q.ds, (D.at a').key₁, allOf (D.at a')⟩ : StageD).base →
      ((⟨a, q.base, allOf (D.at a'), q.ds, (D.at a').key₁, allOf (D.at a')⟩ : StageD).Lin.find?
        fun L =>
          (⟨a, q.base, allOf (D.at a'), q.ds, (D.at a').key₁, allOf (D.at a')⟩ : StageD).key L.no ==
          (⟨a, q.base, allOf (D.at a'), q.ds, (D.at a').key₁, allOf (D.at a')⟩ : StageD).key j).map
            (·.no) = some j) ∧
      (∀ x ∈ p.read, x.1 < 2 ^ 16) ∧ (∀ d ∈ q.ds, ∀ j ∈ d.opens, j < q.base) ∧ q.base ≤ 83 := by
  obtain ⟨n1, n2⟩ := names_along p hA
  obtain ⟨hO, hB⟩ := old_in_scope hZ h p₀ l ht hb hd hq hds n1 n2
  exact ⟨first_in_scope hZ h a' a q.base q.ds hB, low_of_old p hA (hds ▸ hO) hB, hO, hB⟩

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.read_opens
#print axioms VerifiableInference.Desc.First.K2.names_along
#print axioms VerifiableInference.Desc.First.K2.low_of_old
#print axioms VerifiableInference.Desc.First.K2.keys_in_scope
