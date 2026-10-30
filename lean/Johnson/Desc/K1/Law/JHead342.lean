-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Desc/K1/Law/JHead342.lean: THE PREMISE h342 OF `jH_at_reads`
(Johnson/Desc/K1/Law/ArmHeadJ.lean), IN THE FORM THAT `jHead_of_live` LEAVES (`JHead3`,
Johnson/Desc/K1/Law/ArmHeadLive.lean): AT THE REACHED STATES AT THE BORDER 342, INSIDE THE PROMISE
AT 342, AT THE COMPOSED MEANING. One theorem: three calls of Johnson/P4R/Head342.lean.
Why. It is the last fact along "reached" of the output head's half of the field hJH of `K1Left`
(Johnson/Desc/AtSeats/K01KindAll.lean).
  `jHead3_342`: hT by `P4.heard_342`; hRun by `P4.run_342` at the place ⟨1, some 24, 5, .K1⟩ and
  the border `borderOf Wp.y` (`p8K6 Wp 24` is that place with Wp's three values, by its
  definition); hMats by `mats_342`.
Premises. hS, hR, O: the scope and the opening. hWX: the ground's public parameters are Wp. hRch:
the family Rch lies within `RchAt` at the IOP as written in Lean. Public: hOk, hfit, hC, hJ, Nm.
Along Rch: FF. What kind each is: Johnson/P4R/Head342.lean, at its head. NONE SPEAKS OF THE
PROMISE AT 341; NONE OF A STATE THAT NO RUN REACHES.
Limits. `JHead3` says nothing where the state stands in no head or no segment's part is open. That
the premises can be met together is not shown here. No probability: no soundness follows.
Terms: lean/GLOSSARY.md.

-/
import Johnson.Desc.K1.Law.ArmHeadLive
import Johnson.P4R.Head342

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace VerifiableInference.Desc.K1
open OnBytes OnBytes.Params OnBytes.Model
open OnBytes.Model.Verify (borderOf)
open VerifiableInference.OnPublicFiles.Flat (GE)
open VerifiableInference.Desc (Block Chain FileDescription)
open VerifiableInference.Desc.First (S Numbers Meaning pubFit flatPlacesOf FoldData FoldFacts)
open VerifiableInference.Desc.Sound (Frame MsgT onQ linksFull MgData mgAll)
open VerifiableInference.Desc.Kinds VerifiableInference.Desc.Kinds.Head
open VerifiableInference.Desc.Kinds.Head.Law (callKeys)
open VerifiableInference.Desc.Kinds.Head.Law.AtFold (seatsK6C mats_342)
open VerifiableInference.Reads.AtSeat (Nums)
open Johnson.Desc.First.Walk.Tied (RchAt)
open ProofFile (Cl)

/-- **JHead3 at the reached states at 342, inside the promise at 342.** -/
theorem jHead3_342 {P : VerifierAndGoals.PublicFiles} {pp : Inst.Model.ScalesAndPolicy} {lay : ByteArray}
    {F : FileDescription ProofFile.Inst} {Z : ProofFile.Pub} {Bs : ProofFile.PureBase} {base : List (Block S Cl)}
    {c : Chain S Cl} {A : ProofFile.SharedSeat} {B : ProofFile.SecondSeat} {Xi Tok : Type}
    {rows cols nR : ℕ} {Wp : OnBytes.Model.Verify.Public}
    (D : MgData Xi ProofFile.InstPub Tok rows cols nR Wp)
    (Mg : Meaning ProofFile.InstPub (Wit (Fin rows → Fin cols → GE) Tok MsgT))
    (lay6 : OnBytes.Params.ReqLayout) (num : ℕ → ℕ → ℕ) (Fr : Frame)
    (Rch : ℕ → (ProofFile.InstPub × S) × Fr.E.Str → Prop) (d : FoldData)
    (reqW : ProofFile.InstPub → Array UInt32)
    (hS : VerifierAndGoals.InScope P = true) (hR : VerifierAndGoals.readFiles P = .ok pp)
    (O : IM.Open OnBytes.secondHashFunction P.pol lay P.KL F Z Bs base c A B) (hOk : F.planOk = true)
    (hWX : Bs.G₀.W = Wp) (hRch : ∀ k a, Rch k a → RchAt (P4.FD Z A B c) k a)
    (hfit : pubFit (mgAll D Mg).more linksFull (flatPlacesOf linksFull true) = true)
    (FF : FoldFacts Rch (fun a => a.1) d reqW linksFull (flatPlacesOf linksFull true))
    (hd : d.sent = D.sent) (hlay : D.layout = lay6)
    (hC : seatsK6C D.arr D.N Wp lay6 num (num 24 0) 0 D.cs D.shape D.pubD.dS d.L d.M
      (D.sent.arrayOf.getD 24 #[]) (D.N.msgsAt (flatPlacesOf linksFull true)[342]?) = true)
    (hJ : ∀ q, q < 6 → (Wp.HLy.calls.getD q default).lJ =
      (letI := Head.sizesOf Wp.hS; lJ (OnBytes.Model.Head.keyFloor Wp.hS) (callKeys q)))
    (Nm : Nums Wp) :
    ∀ a, Rch 342 a →
      onQ (Fr := Fr) D.N (mgAll D Mg) linksFull (flatPlacesOf linksFull true) (fun a => a) 342 a →
      a.1.2.failed = none → JHead3 Wp (D.N.sent 24 0) D.arr D.N num lay6 a.1.2 := by
  subst hWX
  intro a hr ha hm o aK _ hK
  exact ⟨P4.heard_342 hS hR O hOk a (hRch 342 a hr),
    P4.run_342 hS hR O hOk ⟨1, some 24, 5, .K1⟩ (borderOf Bs.G₀.W.y) hJ Nm a (hRch 342 a hr),
    mats_342 D Mg lay6 num Fr Rch d reqW hfit FF hd hlay hC a hr ha hm aK hK⟩

end VerifiableInference.Desc.K1

#print axioms VerifiableInference.Desc.K1.jHead3_342
