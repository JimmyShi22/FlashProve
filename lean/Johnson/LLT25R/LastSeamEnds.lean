-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/LLT25R/LastSeamEnds.lean (each premise and conclusion of the form "∀ a …,
the promise at border 2 → …" stands besides under a letter E of the statement [a
lemma that takes the promise as a named premise, like `tidy_two`, does not]: what holds beside
the promise; at the ledger: the layer on the last chain's own state. It stands over the ledger
(LastLedger.lean): Oc is a letter. core may also spend the game's own conclusion,
as in LastSeamAt.lean. The
field seam, and core with it, stand under a yes of the seated block):
THE LEDGER's LAW `seam` (the field of `LastRest`, to the letter) FROM THE CORE's FACTS, TWO FACTS AT
THE ENDS OF THE TWO EARLIER CHAINS, AND ONE IMPLICATION: `seam_at_sits` (LastSeamAt.lean)
joined with `groupSits_of_ends` (LastSits.lean) at the ledger's own hand and ended.
  `seatLast t₁ t₂`: the closed seatAt: the seat that the last chain's state's own book gives a
    number (`seatBy (noLast t₁ t₂ firstTree) book`): the one that the words' tables read.
  `HandedSits mine f`: (H1): each member of the own group of what was handed sits, by the first
    chain's own book, at the seat of one of mine, with its shape. `OmegaSits p t₁ mine e`: (H2):
    Omega sits, by the shared chain's book at its end, at the seat of one of mine, whose shape is
    the plan's for Omega.
  `seam_at_ends`: **the field.** ends: wherever the promise at border 2 holds and hand and ended
    return f and e: `HandedSits` and `OmegaSits`.
Limits. core and ends are shown at no state. NO MEMBER. Nothing on soundness.
-/
import Johnson.LLT25R.LastSeamAt
import Johnson.LLT25R.LastSits

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
open VerifiableInference.Desc.Third (S₃ P₁₄)
open _root_.Desc.K14.Law.Fence (CoreFacts)

/-- The seat that the last chain's state's own book gives a number. -/
def seatLast {P : Type} (t₁ t₂ : ℕ) (a0 : P × S₃) (n : ℕ) : Option (ℕ × ℕ) :=
  seatBy (noLast t₁ t₂ a0.2.loc.firstTree) a0.2.book n

/-- (H1) -/
def HandedSits (mine : List Mem) (f : Handed) : Prop :=
  ∀ Gh, f.st.groups[f.own]? = some Gh → ∀ i ∈ Gh.members.toList, ∃ x ∈ mine,
    seatBy noFirst f.book i = some (seatOf x) ∧
      (f.st.oracles[i]?).map (·.shape) = some (x.1.l.get x.2).1

/-- (H2) -/
def OmegaSits (p : P₁₄) (t₁ : ℕ) (mine : List Mem) (e : SharedOut) : Prop :=
  ∃ x ∈ mine, seatBy (noShared t₁) e.book e.omega = some (seatOf x) ∧
    p.S.omega = (x.1.l.get x.2).1

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
  (t₁ t₂ : ℕ)

/- what holds beside the promise at border 2: a letter -/
variable {E : (((FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) × (FL o mk Z
    A N c).S₃) × (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber).E.Str → Prop}

/-- **THE LEDGER's FIELD seam, FROM THE CORE, THE TWO ENDS AND ONE IMPLICATION.** -/
theorem seam_at_ends (hnd : ∀ x ∈ mine, ∀ y ∈ mine, seatOf x = seatOf y → x = y) (core : ∀ a t,
    (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber)) (tiedNumbers N₁ Ns)
    (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂
    MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds hand ended) Oc 2)
        a → E a → Promised cs G smp mine a.1
    (strsOf (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) a.2) → enterOwn a.1.2 = .ok t
    → (∃ rs gs s', (onOwn (proximityTestKind guardedProximityTestParts (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) : Block T12 Cl)).decide
    a.1.2 rs gs = .ok s') → QN (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) (NTuple (frameAt D (allOf D)
                        D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) (H2U.proximityTestParametersAt ⟨3, none, 2, .K12⟩ N.W) no (fun s => r s.st) rd)
    (t, a.2) → CoreFacts cs G (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) (H2U.proximityTestParametersAt
                  ⟨3, none, 2, .K12⟩ N.W) no (fun s => r s.st) smp (memBy mine (seatLast (P := (FL o mk Z A N
                  c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) t₁ t₂) a.1) (· ∈ mine) t a.2 a.1 (strsOf
                  (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber) a.2)) (ends : ∀ a f e, (onQ₃ (Fr :=
                                (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber)) (tiedNumbers N₁ Ns) (tiedMeaning get
                                              (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂ MS)) (promSigS cs G
                                              smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds hand ended) Oc 2) a → E a → hand
                                    (a.1.1.1,
                                    a.1.1.2.1) = some f → ended
                                a.1.1.2.2 = some e → HandedSits mine f ∧ OmegaSits (p14At Z) t₁ mine e) (rowsBack : ∀ a w, (onQ₃
                                (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber)) (tiedNumbers N₁ Ns)
                                (tiedMeaning get (meaningSig cs G arr smp₁ ms₁ decT₁ M₁) (meaningSigS cs G arr smp₂ ms₂ decT₂
                                MS)) (promSigS cs G smp₂ ms₂ stOf bookOf Pm₀) (fillAt (p14At Z) (c2 N).rounds hand ended) Oc 2)
                                    a → E a → insOpenAt (Cells := Cells) (Tok
                                := Tok) (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N c).lastChainFirstTreeNumber)) cs arr (seatLast (P :=
                                              (FL o mk Z A N c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) t₁ t₂) a w → ML.rows
                                a.1.2 w) : ∀ a t st rest G0 Ly D', (onQ₃ (Fr := (frameAt D (allOf D) D.key₃ (FL o mk Z A N
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
                  ML.rows a.1.2 w) a := seam_at_sits o mk Z A N c D cs G arr smp mine get smp₁ smp₂ ms₁ ms₂ decT₁
    decT₂ M₁ MS ML stOf bookOf Pm₀ N₁ Ns Oc hand ended no rd r (seatLast (P := (FL o mk Z A N
    c).XiPub × (FL o mk Z A N c).S₁ × (FL o mk Z A N c).S₂) t₁ t₂) hnd core
    (fun a t G0 hon hE _ ht hG => by
      obtain ⟨f, e, hf, he, hk⟩ := shapeAt_of_onL _ _ _ _ _ _ _ _ hon
      exact groupSits_of_ends _ _ f e a.1.2 t G0 t₁ t₂ mine hk ht hG (ends a f e hon hE hf he).1
        (ends a f e hon hE hf he).2)
    rowsBack

end LLT25

#print axioms LLT25.seam_at_ends
