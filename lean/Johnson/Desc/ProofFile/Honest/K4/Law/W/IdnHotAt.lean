-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0

/-
Johnson/Desc/ProofFile/Honest/K4/Law/W/IdnHotAt.lean: CONDITIONAL.

Not shown here. EVERY HYPOTHESIS BELOW IS ASKED; NO STATEMENT IN THIS FILE LEADS TO ANY OF THEM. c:
the sentence of a table's item `Item.constr (2 * g) p` at the witness that the Script makes:
Law/W/OpenAtHead.lean takes that of the part `.idn` out of the thread, where the item is open in
front of K4's member (Johnson/Desc/First/Borders.lean). hi: the Script's cells hold an index: it
speaks of a run's input and of no state: it is meant to come from the thread's clause that the input
is valid (`indexIs_thr`, Law/IndexIs.lean, has it from one hypothesis under that clause). hg: g <
12. hp: the part is not lookDigits. The side library AtFullSide proves, with no hypothesis, that h
has a member at one place (AtFullSide.Top.headMember_zFull, AtFullSide/Top/HeadMemberAtFull.lean,
whose own Limits say what it is worth). Of h together with hi, hg, hp and c (`part_head`) no example
is known to us; `partG_of_constr` takes no h: its hypotheses are hc, hp, hh, hd' and hM. THE FULL
SIZE ALONE, and the format's second hash function alone (`OnBytes.secondHashFunction`): at a smaller plan nothing here
applies. Nothing on soundness, on completeness or on any other property.
No property is claimed.
WHAT THIS FILE's IMPORTS REACH, by a program's walk from import to import that stops, unopened, at
every module under Johnson/Goal/, Johnson/D/, Johnson/Bridge/ or ThirdParty/, at every module whose
name begins Cb.Bridge, and at the names RecCompile.Honest…, RecCompile.Both… and RecCompile.PassH…:
it stopped at 19 modules under Johnson/Goal/ and at 4 under Johnson/Bridge/; it saw 46 modules whose
names hold RecCompile, none under Johnson/D/ or ThirdParty/, none that begins Cb.Bridge and none of
the three names. What lies behind the 23 is not counted: all the numbers are floors. They come with
h and with Johnson/P5J/MeansQ.lean.

What the sentence of a table's item at a layers' segment says, at the thread of the first chain with
the library's own values laid in (`lettersHead`, Honest/Thread/FirstHead.lean): the library's
`partG` at the group's list. Law/W/IdnHead.lean and Law/W/EmbHead.lean go on from it, towards fields
of the hypothesis `ItemRight` (Law/W/SlotsOfStand.lean) on the state behind the step of the
feed-forward layers' own rounds (sub-protocol K4). Statements with their proofs.

How. At that thread an item's sentence is the library's `constrQAt` (Johnson/P5J/MeansQ.lean) by
unfolding; at an even segment that is not the head's it is `partG`, whose part `.idn` holds
`NormField` and `EmbField` at the list (hid w).MG g.

  `partG_of_constr`   the sentence at an even segment 2 g that is not the head's, at a part other
      than lookDigits, at an index that the decoded table holds: `partG` at group g.
  `part_head`   **that at the thread, from an item's sentence.**
-/
import Johnson.Desc.ProofFile.Honest.Thread.FirstHead
import Johnson.P5J.RowsAtMg
import Johnson.Road.K4.W.IdnOfField
import Johnson.Road.K4.W.MatsOfList

set_option autoImplicit false
set_option relaxedAutoImplicit false

/- no default table of scales is in sight: a statement that reads a table says which -/
attribute [-instance] Inst.Model.Scl.ref

namespace ProofFile.Honest.K4.W
open OnBytes OnBytes.Model
open OnBytes.Maker (WholeD)
open Inst.Model (ppref)
open VerifiableInference.Desc (Place Chain Strs)
open VerifiableInference.Desc.First (Item)
open VerifiableInference.Desc.Sound (MsgT oneDec)
open VerifiableInference.OnPublicFiles (headLink)
open VerifiableInference.OnPublicFiles.Flat (Holds GE)
open P5J (AtMgA CellsM TS TPart TReq HidAt partG constrQAt)
open ProofFile.Honest.FirstThread (Script WtF lettersHead)

/-- **The library's sentence at an even segment that is not the head's is `partG` at its group.**
CONDITIONAL: on hc, hp, hh, hd' and hM. -/
theorem partG_of_constr {X : Verify.Public} {P W : Type} {rows cols hd : ℕ}
    {put : TReq → Fin ppref.V → TReq} {Hh : HidAt X P W rows cols}
    {hP : TPart → Cm.Idx → P × TS → Strs → W → Prop} {dP : ℕ → P × TS → Strs → W → Prop} {g : ℕ}
    {p : TPart} {a : P × TS} {y : Strs} {w : W} {M : Fin rows → Fin cols → GE} {i : Cm.Idx}
    (hc : constrQAt hd put Hh hP dP (2 * g) p a y w) (hp : p ≠ .lookDigits) (hh : 2 * g ≠ hd)
    (hd' : Hh.dec a y = some M) (hM : Holds M i) :
    partG X i (put (Hh.req a) (Hh.hid w).tok).val (Hh.hid w).MG g p := by
  unfold constrQAt at hc
  rw [if_neg hp] at hc
  have q := hc.2 M i hd' hM
  rw [if_neg hh, if_pos (Nat.mul_mod_right 2 g), Nat.mul_div_cancel_left g (by norm_num)] at q
  exact q

variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain TS ProofFile.Cl} {xh : VerifiableInference.Desc.First.Look.Place}
  (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF xh) {Bk : ProverCoinCounts} {W₀ Rc Ky Tr X₀ X' : Type}
  (H : Prover W₀ Rc ProofFile.Inst Ky Tr X₀ X')
  (Q : Script Bk (Local W₀ Rc ProofFile.Inst Tr) (CellsM OnBytes.Flat.numsFull) P5J.At.Tok MsgT)
  (test : Nat → TS → Option String) (carryX : Nat → ProofFile.InstPub × TS → Strs → WtF → Prop)
  (item n₁ n₂ b₀ : Nat) (Vd : Local W₀ Rc ProofFile.Inst Tr → Prop)
  (Rd : Nat → Local W₀ Rc ProofFile.Inst Tr → TS → Prop) (Kp : Place → TS → TS → Prop)
  (w₁ : Local W₀ Rc ProofFile.Inst Tr)

/-- **An item's sentence at the thread is `partG` at the group**, at a part other than lookDigits.
k: a run's coins. v: an input. s: any state. y: any strings. ds: any list of challenges. i: an index
that the Script's cells hold. CONDITIONAL: on h, hi, hg, hp and c. -/
theorem part_head (k : Coins Bk) (v : Local W₀ Rc ProofFile.Inst Tr) (s : TS) (y : Strs)
    (ds : List Fmt.Drawn) {i : Cm.Idx} (hi : Holds (Q.cells v) i) {g : ℕ} (hg : g < 12)
    {p : TPart} (hp : p ≠ .lookDigits)
    (c : (lettersHead h H Q test carryX item n₁ n₂ b₀ Vd Rd Kp w₁).thread.means v
      (Item.constr (2 * g) p) (v.x.pub, s) y (Q.wit k v ds)) :
    ∃ x, partG (P5J.At.X Zp) i x (h.𝔇.H.hid (Q.wit k v ds)).MG g p := by
  have e24 := P5J.headLink_in_scope h.scope h.reads h.pubOne
  have c' : constrQAt (headLink (P5J.At.X Zp)) h.𝔇.put
      (oneDec (fun _ _ => some (Q.cells v)) h.𝔇.H) h.𝔇.headPart h.𝔇.digitsPart (2 * g) p
      (v.x.pub, s) y (Q.wit k v ds) := c
  have hh : 2 * g ≠ headLink (P5J.At.X Zp) := by
    rw [e24]
    omega
  have q := partG_of_constr (Hh := oneDec (fun _ _ => some (Q.cells v)) h.𝔇.H) (M := Q.cells v) c'
    hp hh rfl hi
  exact ⟨_, q⟩

end ProofFile.Honest.K4.W

#print axioms ProofFile.Honest.K4.W.partG_of_constr
#print axioms ProofFile.Honest.K4.W.part_head
