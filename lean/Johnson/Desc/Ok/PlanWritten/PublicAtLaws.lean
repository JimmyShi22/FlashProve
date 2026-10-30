-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/Ok/PlanWritten/PublicAtLaws.lean: laws on the public part of a stage and on the
planner's text with the second hash function as an argument (`publicOfO`, `plannedAtO`,
Johnson/Desc/Ok/PlanWritten/PublicAt.lean).

They are tools: they hold of all public files, and no description of the protocol is named.

Statements and proofs.

  One equation for each twin, at the second hash function itself: `tableDigestO_older`,
    `tableHeldO_older`, `textTHO_older`, `parDigestsO_older`, `hParOfO_older`, `hParO_older`,
    `Attention.callsDigestO_older`, `Attention.configO_older`, `callsDigestO_older`: the twin at
    `secondHashFunction` is the library's routine. For the tree hash the library has `olderTK_eq`
    (OnBytes/Tie/Decl/RequestItemLaw.lean).
  `publicOfO_older`: publicOfO secondHashFunction pol KL layout = publicOf pol KL layout. So every law of the
    library on what `publicOf` returns holds of what `publicOfO secondHashFunction` returns.
  `plannedAtO_older`: plannedAtO secondHashFunction pol KL layout c = plannedAt pol KL layout c
    (OnBytes/Tie/ChainsAtCfg.lean).
  `publicOfO_scan`, at every o: the scan in what `publicOfO o` returns is the scan of the parameter
    file (the like of `publicOf_scan`, OnBytes/Model/VerifyDerives.lean).
  `tableHeldO_iff`, at every o: the test on a public table says yes if and only if the parameter
    file gives no digest for that table, or the digest that it gives is o's, at the number 72, of
    the table's words. So the argument bears weight. `tableHeldO_no`: where the file gives a digest,
    the test says no at every o whose value there is another.
  `bne_iff`, a helper: the test != on two strings of bytes says yes if and only if they differ.

Limits. The equations are at `secondHashFunction` alone. At another o nothing says that `publicOfO o` returns a
value. That the copy has every test of the library's text is what the equation says at `secondHashFunction`; at
another o it is a matter of reading the two texts side by side. What does not depend on o is told in
Johnson/Desc/Ok/PlanWritten/PublicAtTwo.lean. Nothing on soundness.
-/
import Johnson.Desc.Ok.PlanWritten.PublicAt
import OnBytes.Tie.Decl.RequestItemLaw
import OnBytes.Model.VerifyDerives
import OnBytes.Tie.ChainsAtCfg
import Fmt.ParsedReadFileLaws

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.PlanWritten

open OnBytes OnBytes.Model OnBytes.Model.Verify
open OnBytes.Params (exc_bind)
open OnBytes.Tie.Decl.RequestItemLaw (olderTK_eq)

/-! ## The twins at the second hash function itself -/

theorem tableDigestO_older : tableDigestO secondHashFunction = tableDigest := rfl

theorem tableHeldO_older : tableHeldO secondHashFunction = tableHeld := rfl

theorem textTHO_older : textTHO secondHashFunction = textTH := by
  funext text
  unfold textTHO textTH
  simp only [olderTK_eq]
  rfl

theorem parDigestsO_older : parDigestsO secondHashFunction = parDigests := by
  funext pol KL layout
  unfold parDigestsO parDigests
  simp only [textTHO_older, olderTK_eq]
  rfl

theorem hParOfO_older : hParOfO secondHashFunction = hParOf := by
  funext d
  unfold hParOfO hParOf
  simp only [olderTK_eq]
  rfl

theorem hParO_older : hParO secondHashFunction = hPar := by
  funext pol KL layout
  unfold hParO hPar
  rw [parDigestsO_older, hParOfO_older]

theorem Attention.callsDigestO_older :
    Attention.callsDigestO secondHashFunction = OnBytes.Attention.callsDigest := rfl

theorem Attention.configO_older : Attention.configO secondHashFunction = OnBytes.Attention.config := by
  funext P y s midQ
  unfold Attention.configO OnBytes.Attention.config
  simp only [tableHeldO_older, Attention.callsDigestO_older]
  rfl

theorem callsDigestO_older : callsDigestO secondHashFunction = callsDigest := rfl

/-- **At the second hash function itself the new text is the old text.** -/
theorem publicOfO_older (pol KL : ByteArray) (layout : Option ByteArray) :
    publicOfO secondHashFunction pol KL layout = publicOf pol KL layout := by
  unfold publicOfO publicOf
  simp only [tableHeldO_older, hParO_older, Attention.configO_older, callsDigestO_older]

/-- The planner's text with the digest as an argument: at the second hash function itself the new
text is the old text. -/
theorem plannedAtO_older (pol KL : ByteArray) (layout : Option ByteArray) (c : ByteArray) :
    plannedAtO secondHashFunction pol KL layout c = OnBytes.Tie.plannedAt pol KL layout c := by
  unfold plannedAtO OnBytes.Tie.plannedAt
  rw [publicOfO_older]

/-! ## At every o -/

/-- The scan in the public part is the scan of the parameter file. -/
theorem publicOfO_scan {o : Nat → ByteArray → ByteArray} {pol KL : ByteArray}
    {layout : Option ByteArray} {X : Public} (h : publicOfO o pol KL layout = .ok X) :
    polScan pol = .ok X.P := by
  unfold publicOfO at h
  obtain ⟨⟨P, y⟩, h0, h⟩ := exc_bind h
  have e : X.P = P := by
    dsimp only at h
    repeat' first
      | (obtain ⟨_, _, h⟩ := exc_bind h)
      | (split at h)
    all_goals (cases h; rfl)
  rw [e]
  exact polLayout_scan h0

/-- The test != on two strings of bytes. -/
theorem bne_iff (a b : ByteArray) : (a != b) = true ↔ a ≠ b := by
  constructor
  · intro h e
    rw [e] at h
    have h' : (!(b == b)) = true := h
    rw [Fmt.bytes_beq_self] at h'
    cases h'
  · intro h
    show (!(a == b)) = true
    cases hb : (a == b) with
    | false => rfl
    | true => exact absurd (Fmt.eq_of_bytes_beq a b hb) h

/-- **The test on a public table, at every o.** -/
theorem tableHeldO_iff (o : Nat → ByteArray → ByteArray) (P : PolScan) (t : PublicTable)
    (table : Array Nat) :
    tableHeldO o P t table = .ok () ↔
      ∀ d, P.tableExpected t = some d →
        d = o tableHashNumber (table.foldl (fun b x => b ++ word32 x) ByteArray.empty) := by
  cases hE : P.tableExpected t with
  | none => simp [tableHeldO, refuseIf, hE]
  | some d0 =>
    by_cases hd : d0 = o tableHashNumber (table.foldl (fun b x => b ++ word32 x) ByteArray.empty)
    · have hb : (d0 != o tableHashNumber
          (table.foldl (fun b x => b ++ word32 x) ByteArray.empty)) = false := by
        cases hx : (d0 != o tableHashNumber
            (table.foldl (fun b x => b ++ word32 x) ByteArray.empty)) with
        | false => rfl
        | true => exact absurd hd ((bne_iff _ _).1 hx)
      constructor
      · intro _ d e
        obtain rfl := Option.some.inj e
        exact hd
      · intro _
        simp [tableHeldO, tableDigestO, refuseIf, hE, hb]
    · have hb := (bne_iff _ _).2 hd
      constructor
      · intro h
        simp [tableHeldO, tableDigestO, refuseIf, hE, hb] at h
      · intro h
        exact absurd (h d0 rfl) hd

/-- Where the file gives a digest the test says no at every o whose value is another. -/
theorem tableHeldO_no {o : Nat → ByteArray → ByteArray} {P : PolScan} {t : PublicTable}
    {table : Array Nat} {d : ByteArray} (hE : P.tableExpected t = some d)
    (hd : d ≠ o tableHashNumber (table.foldl (fun b x => b ++ word32 x) ByteArray.empty)) :
    tableHeldO o P t table ≠ .ok () := fun h => hd ((tableHeldO_iff o P t table).1 h d hE)

end VerifiableInference.PlanWritten

#print axioms VerifiableInference.PlanWritten.tableDigestO_older
#print axioms VerifiableInference.PlanWritten.tableHeldO_older
#print axioms VerifiableInference.PlanWritten.textTHO_older
#print axioms VerifiableInference.PlanWritten.parDigestsO_older
#print axioms VerifiableInference.PlanWritten.hParOfO_older
#print axioms VerifiableInference.PlanWritten.hParO_older
#print axioms VerifiableInference.PlanWritten.Attention.callsDigestO_older
#print axioms VerifiableInference.PlanWritten.Attention.configO_older
#print axioms VerifiableInference.PlanWritten.callsDigestO_older
#print axioms VerifiableInference.PlanWritten.publicOfO_older
#print axioms VerifiableInference.PlanWritten.plannedAtO_older
#print axioms VerifiableInference.PlanWritten.publicOfO_scan
#print axioms VerifiableInference.PlanWritten.bne_iff
#print axioms VerifiableInference.PlanWritten.tableHeldO_iff
#print axioms VerifiableInference.PlanWritten.tableHeldO_no
