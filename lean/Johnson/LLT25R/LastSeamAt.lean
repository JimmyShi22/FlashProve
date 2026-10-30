-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastSeamAt.lean (each premise and conclusion of the form "∀ a …,
the promise at border 2 → …" stands besides under a letter E of the statement [a
lemma that takes the promise as a named premise, like `tidy_two`, does not]: what holds beside
the promise; at the ledger: the layer on the last chain's own state;
the two later tables' own condition Oc is a letter;
core may also spend THE GAME's OWN CONCLUSION, `QN π (NTuple …)` at what the door
returns: K12's files' law on `siteL` spends a yes that `NTuple` holds;
THE FIELD seam STANDS UNDER A
YES OF THE SEATED BLOCK, AND SO DOES core: the facts may be had from the block's own tests):
THE LEDGER's LAW `seam` (the field of `LastRest`,
LastLedger.lean, to the letter) AT THE PROOF FILE's OWN DESCRIPTION AND THE FILLINGS THAT LIE,
FROM TWO BUNDLES OF PLAIN FACTS AND ONE IMPLICATION.
  `candN_mono`: the table's conclusion is monotone in ins.
  `seam_at`: **the field seam FROM: core: `CoreFacts` (Johnson/Desc/Sound/SeamFacts.lean)
    at what the seat's door returns, inside the promise at border
    2, WHERE THE SEATED BLOCK SAYS YES AT SOME ROUNDS · cover: `CoverAt` (LastSeamRows.lean)
    there · rowsBack: "every open row of the own group holds of the words that the witness's tables
    give" gives ML.rows: the identity where ML.rows IS that sentence.** By `seam_of_facts`.
  `seam_at_sits`: the same at the closed mem `memBy`: cover gives way to `GroupSits` (by the
    record's own book every member of the group under test sits at the seat of one of mine, with its
    shape) and "no two of mine have one seat".
The new letters: mem (which member of the lists an oracle message's number names, at the outer
record) and seatAt (at which seat an oracle message's number sits, read off the record). The reader
of a typed message is laid: `tabP`.
Limits. core and cover are shown at no record. NO MEMBER. Nothing on soundness.
-/
import Johnson.LLT25R.LastLedger
import Johnson.LLT25R.LastSeamRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

noncomputable section

namespace LLT25
open OnBytes OnBytes.Params OnBytes.Slice OnBytes.Slice.ProxRun OnBytes.Maker Fo.Peel Cb
    Johnson.Pack
open Iop Prob _root_.Run
open VerifiableInference VerifiableInference.OnPublicFiles VerifiableInference.OnPublicFiles.Last
open VerifiableInference.Desc VerifiableInference.Desc.K12 VerifiableInference.Desc.Sound
open VerifiableInference.Desc.Plain VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Shared VerifiableInference.Desc.Last
open VerifiableInference.Desc.K12.Seat (enterOwn leaveOwn onOwn)
open VerifiableInference.Desc.Third (SharedOut)
open VerifiableInference.Desc.First (S ModelPart Item Meaning Numbers openSets sampledIn start)
open ProofFile (SecondHashFunctionArgument LinksBy SharedSeat Cl)
open ToldDesc (p14At)
open H2K.Pin (NTuple)
open H2K.Pub (johOk batV0)
open H2K.First (batOneOk)
open H2K.Pin (tabP)
open _root_.Desc.K14.Law.Fence (CoreFacts)

/-- The table's conclusion is monotone in ins. -/
theorem candN_mono {Pp S₃' Cells Tok Xi : Type} (cs : OnBytes.Codes) (G : FileDescription Xi)
    (arr : ℕ → ℕ → ℕ)
    (smp : (Pp × S₃') → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
    (Fr : Frame) (mine : List Mem)
    (ins ins' : (Pp × S₃') × Fr.E.Str → Wit Cells Tok MsgT → Prop) (a : (Pp × S₃') × Fr.E.Str)
    (h : ∀ w, ins a w → ins' a w) (hc : candN cs G arr smp Fr mine ins a) :
    candN cs G arr smp Fr mine ins' a := by
  obtain ⟨c, h1, h2⟩ := hc
  exact ⟨c, h1, fun w w' hl => h w' (h2 w w' hl)⟩

variable (o : SecondHashFunctionArgument) (mk : LinksBy) (Z : ProofFile.Pub) (A : SharedSeat) (N : H2U.Places4)
  (c : Chain S Cl) {Cells Tok P₀ : Type} (D : WholeD)
  (cs : OnBytes.Codes) {Xi' : Type} (G : FileDescription Xi') (arr : ℕ → ℕ → ℕ)
  (smp : (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) × (FL o mk Z A N
      c).S₃) → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (decT : (ℕ → Option (ℕ × List UInt64)) → (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o
      mk Z A N c).S₂) × (FL o mk Z A N c).S₃) → Option Cells)
  (c₀' : Cells) (dB : RDT) (dt : List RDT) (mine : List Mem)
  (get : (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ → P₀ × First.S)
  (smp₁ : P₀ × First.S → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om i).Smp)
  (smp₂ : (FL o mk Z A N c).S₂ → (s : Sending) → (i : Fin s.l.length) → Option ((sigOf cs s.l).om
      i).Smp)
  (ms₁ ms₂ : List Mem) (decT₁ : (ℕ → Option (ℕ × List UInt64)) → P₀ × First.S → Option Cells)
  (decT₂ : (ℕ → Option (ℕ × List UInt64)) → (FL o mk Z A N c).S₂ → Option Cells)
  (M₁ : Meaning P₀ (Wit Cells Tok MsgT)) (MS : MeaningS (FL o mk Z A N c).S₂ ((FL o mk Z A N
      c).XiPub × (FL o mk Z A N c).S₁) (Wit Cells Tok MsgT))
  (ML : MeaningL (FL o mk Z A N c).S₃ (Wit Cells Tok MsgT)) (stOf : (FL o mk Z A N c).S₂ →
      OnBytes.Statement)
  (bookOf : (FL o mk Z A N c).S₂ → OnBytes.TreeBook) (Pm₀ : PromMeaning (FL o mk Z A N c).S₂) (N₁ :
      Numbers) (Ns : NumbersS)
  (links : List ModelPart) (ps : List VerifiableInference.Desc.Place)
  (Oc : (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ → Strs → Prop)
  (hand : (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ → Option Handed) (ended : (FL o mk Z A N
      c).S₂ → Option SharedOut)
  (num : Fmt.TreeSource → ℕ) (no : ℕ → ℕ) (rd : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ)
  (mem : (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) × (FL o mk Z A N
      c).S₃) → ℕ → Option Mem) (seatAt : (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk
      Z A N c).S₂) × (FL o mk Z A N c).S₃) → ℕ → Option (ℕ × ℕ))

/- what holds beside the promise at border 2: a letter -/
variable {E : (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) × (FL o mk Z
    A N c).S₃) × (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber).E.Str → Prop}

/-- **THE LEDGER's FIELD seam, FROM TWO BUNDLES OF PLAIN FACTS AND ONE IMPLICATION.** -/
theorem seam_at (core : ∀ a t, (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N
    c).lastChainFirstTreeNumber)) (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁)
                  (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt
                  (p14At Z) (c2 N).rounds hand ended) Oc 2) a → E a → Promised cs G smp mine a.1 (strsOf (frameAt
                      D
                      (allOf D) D.key₃ (FL o mk Z A N
                  c).lastChainFirstTreeNumber) a.2) → enterOwn a.1.2 = .ok t → (∃ rs gs s', (onOwn (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3,
                                                                                   none, 2, .K12⟩ N.W) : Block T12 Cl)).decide a.1.2 rs gs = .ok s') → QN (H2U.proximityTestParametersAt ⟨3, none, 2,
                                                                                                       .K12⟩ N.W) (NTuple (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) (H2U.proximityTestParametersAt ⟨3,
                                                                                                                                         none, 2, .K12⟩ N.W) no (fun s => r s.st) rd) (t, a.2) → CoreFacts cs G (frameAt D (allOf D)
                                                                                                                                         D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) no (fun s => r s.st) smp
    (mem a.1) (· ∈ mine) t a.2 a.1 (strsOf (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber)
    a.2)) (cover : ∀ a t G0, (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber))
    (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G
    arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds
    hand ended) Oc 2) a → E a → Promised cs G
    smp mine a.1 (strsOf (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) a.2) → enterOwn
    a.1.2 = .ok t → t.st.groups[t.g]? = some G0 → CoverAt mine mem seatAt a.1 t G0) (rowsBack : ∀ a
    w, (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber)) (tiedNumbers N₁ Ns)
    (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂
    MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds hand ended) Oc 2)
        a → E a → insOpenAt (Cells := Cells) (Tok
    := Tok) (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber)) cs arr seatAt a w →
    ML.rows a.1.2 w) : ∀ a t st rest G0 Ly D', (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A
    N c).lastChainFirstTreeNumber)) (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁)
                  (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt
                  (p14At Z) (c2 N).rounds hand ended) Oc 2) a → E a → Promised cs G smp mine a.1 (strsOf (frameAt
                      D
                      (allOf D) D.key₃ (FL o mk Z A N
                  c).lastChainFirstTreeNumber) a.2) → enterOwn a.1.2 = .ok t → Fixes (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) t st
    rest G0 Ly D' → NTuple (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) (H2U.proximityTestParametersAt ⟨3,
                                      none, 2, .K12⟩ N.W) no (fun s => r s.st) rd (t, a.2) st rest G0 Ly D' → (∃ rs gs s', (onOwn (proximityTestKind
                                      guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Cl)).decide a.1.2 rs gs = .ok s') →
    candN cs G arr smp (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) mine (fun a w =>
                  ML.rows a.1.2 w) a := fun a t st rest G0 Ly D' hon hE hP ht hf hN hY => candN_mono cs G arr smp
        _
    mine _ _ a (fun w hw => rowsBack a w hon hE hw) (seam_of_facts _ _ _ _ _ _ _ _ cs G arr smp mine
        _
    no _ rd mem (fun x m => tabP cs (x.1.l.get x.2).1 m) seatAt (fun a => (∃ rs gs s', (onOwn (proximityTestKind
    guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Cl)).decide a.1.2 rs gs = .ok s') ∧ ∀ t,
    enterOwn a.1.2 = .ok t → QN (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) (NTuple (frameAt D (allOf D)
                        D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) no (fun s => r s.st) rd)
    (t, a.2)) (fun _ _ _ _ => rfl) (fun a t hon hE hP ht hY => core a t hon hE hP ht hY.1 (hY.2 t
        ht))
    cover a t st rest G0 Ly D' hon hE hP ht hf hN ⟨hY, fun _ ht' => (Except.ok.inj (ht.symm.trans
    ht')) ▸ ⟨st, rest, G0, Ly, D', hf, hN⟩⟩)

/-- **THE SAME AT THE CLOSED mem**: the one of mine at whose seat the record's own book lays the
number. -/
theorem seam_at_sits (hnd : ∀ x ∈ mine, ∀ y ∈ mine, seatOf x = seatOf y → x = y) (core : ∀ a t,
    (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber)) (tiedNumbers N₁ Ns)
    (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂
    MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds hand ended) Oc 2)
        a → E a → Promised cs G smp mine a.1
    (strsOf (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) a.2) → enterOwn a.1.2 = .ok t
    → (∃ rs gs s', (onOwn (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Cl)).decide
    a.1.2 rs gs = .ok s') → QN (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) (NTuple (frameAt D (allOf D)
                        D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) no (fun s => r s.st) rd)
    (t, a.2) → CoreFacts cs G (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) (H2U.proximityTestParametersAt
                  ⟨3, none, 2, .K12⟩ N.W) no (fun s => r s.st) smp (memBy mine seatAt a.1) (· ∈ mine) t a.2 a.1
    (strsOf (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) a.2)) (cover : ∀ a t G0, (onQ₃
                  (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber)) (tiedNumbers N₁ Ns)
                  (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂
                  MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds hand ended) Oc 2)
                      a → E a → Promised cs G smp mine a.1
                  (strsOf (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) a.2) → enterOwn a.1.2 = .ok t
                  → t.st.groups[t.g]? = some G0 → GroupSits mine seatAt a.1 t G0) (rowsBack : ∀ a w, (onQ₃ (Fr :=
                  (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber)) (tiedNumbers N₁ Ns) (tiedMeaning get
                                (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) (promSigS cs G
                                smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds hand ended) Oc 2) a → E a → insOpenAt
                      (Cells
                      := Cells) (Tok := Tok) (Fr :=
                  (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber)) cs arr seatAt a w → ML.rows a.1.2 w)
    : ∀ a t st rest G0 Ly D', (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N
    c).lastChainFirstTreeNumber)) (tiedNumbers N₁ Ns) (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁)
                  (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt
                  (p14At Z) (c2 N).rounds hand ended) Oc 2) a → E a → Promised cs G smp mine a.1 (strsOf (frameAt
                      D
                      (allOf D) D.key₃ (FL o mk Z A N
                  c).lastChainFirstTreeNumber) a.2) → enterOwn a.1.2 = .ok t → Fixes (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) t st
    rest G0 Ly D' → NTuple (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) (H2U.proximityTestParametersAt ⟨3,
                                      none, 2, .K12⟩ N.W) no (fun s => r s.st) rd (t, a.2) st rest G0 Ly D' → (∃ rs gs s', (onOwn (proximityTestKind
                                      guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Cl)).decide a.1.2 rs gs = .ok s') →
    candN cs G arr smp (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) mine (fun a w =>
                  ML.rows a.1.2 w) a := seam_at o mk Z A N c D cs G arr smp mine get smp₁ smp₂ ms₁ ms₂ decT₁ decT₂
    M₁ MS ML stOf bookOf Pm₀ N₁ Ns Oc hand ended no rd r (memBy mine seatAt) seatAt core (fun
    a t G0 hon hE hP ht hG => cover_of_sits mine seatAt hnd a.1 t G0 (cover a t G0 hon hE hP ht hG))
    rowsBack

end LLT25

#print axioms LLT25.seam_at
#print axioms LLT25.seam_at_sits
