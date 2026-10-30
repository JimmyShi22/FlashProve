-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1L20R/FrameLowAll.lean:
the field "low" of the frame's condition at the seated term (FrameOwed4,
FrameFourAll.lean) FROM ONE TEST WITH CODE ON PUBLIC DATA: fenceFit's yes at the head's own numbers.

  low_atAll         where fenceFit (dmOf h).N linksFull (the written list) accepts: at EVERY number
                    k of the first chain's row: the OOD-sampled oracle messages whose pin is open at
                    border k sit in trees below the base of the piece at k. By
                    low_withTold (Johnson/Top/H0/Walk/FrameBase.lean) at numbers_atAll
                    (FramePaidAll.lean)
  FrameOwed4b       FrameOwed4 with the test "fence" in the place of the field "low"
  frame_kind_of4b   h.Kind L KindName.frame from FrameOwed4b

Limits. fenceFit's yes is a premise; it is shown at no numbers here. No field of FrameOwed4b is
shown here. No soundness statement.

-/
import Johnson.P1L20R.FrameFourAll

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

attribute [-instance] Inst.Model.Scl.ref

namespace P1L20

open OnBytes.Maker OnBytes.Flat OnBytes.Slice KObj
open VerifiableInference.Desc (Block Chain FileDescription Place KindName Strs Wit)
open VerifiableInference.Desc.Sound
open VerifiableInference.Desc.First (S flatPlacesOf fenceFit)
open VerifiableInference.Desc.First.K2Caller (spotsFitB)
open Johnson.Desc.First.Walk.Tied
open ProofFile (Cl)
open P5J (AtMgA Free F0T)

section
variable {Z : VerifierAndGoals.PublicFiles} {D : WholeD} {r : LPFD.Full.RunPF} {Zp : ProofFile.Pub} {Np : H2U.Places4}
  {cF : Chain S Cl} {x : VerifiableInference.Desc.First.Look.Place}

set_option maxHeartbeats 4000000 in
/-- **The field "low", at every number of the row, from fenceFit's yes.** -/
theorem low_atAll (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (hf : fenceFit (dmOf h).N linksFull (flatPlacesOf linksFull true) = true) :
    ∀ (k : ℕ), k ≤ (flatPlacesOf linksFull true).length → ∀ q,
      (h.toAtMg.row L)[k]? = some q → LowAt (dmOf h).N (openL9 k) (Piece.base q) := by
  intro k hk q hq
  have Ft := threeCap_fits L.e₁ L.e₂ L.e₃ L.dW L.wEnd (data_atAll h) h.laid.planOk q₁ q₂ q₃
  rw [numbers_atAll h] at hf ⊢
  exact low_withTold (F0T OnBytes.secondHashFunction Zp Np cF) "proof file" (D.at frS.P.T.a) (data_atAll h)
    (threeCap (F0T OnBytes.secondHashFunction Zp Np cF) (D.at frS.P.T.a) L.c₁ L.k₁ L.c₂ L.k₂ L.c₃ L.k₃ L.e₁
      L.e₂ L.e₃ L.dW L.wEnd)
    (threeCap_ofDesc L.e₁ L.e₂ L.e₃ L.dW L.wEnd (data_atAll h) h.laid.planOk q₁ q₂ q₃)
    Ft.tiled₁ Ft.data₁
    (fun b hb => (((FileDescription.planOk_ok _).1 h.laid.planOk).blocks₁ b hb).2) Ft.base₁ hq
    (n0All Zp cF) linksFull (flatPlacesOf linksFull true) places_nodup_full hk hf

/-- **WHAT IS LEFT IN FRONT OF THE FRAME's LAW AT THE SEATED TERM**, "low" cut down to a test. -/
structure FrameOwed4b (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok) : Prop where
  /-- a test with code on public data: no two code switches open the same group, and each is of the
  sort (link, output head, finish) that its segment's number asks -/
  spots : spotsFitB Zp = true
  /-- a fact on public data: the request's shape has 25 links -/
  links25 : Zp.s₀.check.frame.shape.link.length = 25
  /-- a test with code on public data: every seat whose pin is open at a border lies in a tree that
  the sub-protocols in front have told -/
  fence : fenceFit (dmOf h).N linksFull (flatPlacesOf linksFull true) = true
  /-- of every statement that is reached in front of one of the 51 numbers and bears no mark: the
  book is in order from tree 0 on, it fits, the carried rows name messages that have a place -/
  kn : ∀ k a, h.toAtMg.rch k a → a.1.2.failed = none →
    KnTight 0 k (a.1.1, a.1.2) (strsOf (FrAll D) a.2)
  /-- the seal's tie (other files' to show) -/
  sealTie : ∀ q, (h.toAtMg.row L)[357]? = some q →
    TiedAtR (Fr := FrAll D) (dmOf h).N (mgAll (dmOf h) mgBase) linksFull
      (flatPlacesOf linksFull true) (fun a => a) h.toAtMg.rch 357 (q.withMap (h.toAtMg.ex L 357))
  /-- the 25 ties behind the batching (other files' to show) -/
  behindTies : ∀ l, l < 25 → ∀ q, (h.toAtMg.row L)[behindIx l]? = some q →
    TiedAtR (Fr := FrAll D) (dmOf h).N (mgAll (dmOf h) mgBase) linksFull
      (flatPlacesOf linksFull true) (fun a => a) h.toAtMg.rch (behindIx l)
      (q.withMap (h.toAtMg.ex L (behindIx l)))

/-- **THE KIND "frame" AT THE SEATED TERM, from these.** -/
theorem frame_kind_of4b (h : AtMgA OnBytes.secondHashFunction Z D r Zp Np cF x)
    (L : Free numsFull D (F0T OnBytes.secondHashFunction Zp Np cF) P5J.At.Tok)
    (q₁ : (F0T OnBytes.secondHashFunction Zp Np cF).first.blocksInOrder = L.c₁ :: L.k₁)
    (q₂ : (F0T OnBytes.secondHashFunction Zp Np cF).shared.blocksInOrder = L.c₂ :: L.k₂)
    (q₃ : (F0T OnBytes.secondHashFunction Zp Np cF).second.blocksInOrder = L.c₃ :: L.k₃)
    (W : FrameOwed4b h L) : h.Kind L KindName.frame :=
  frame_kind_of4 h L q₁ q₂ q₃
    { spots := W.spots
      links25 := W.links25
      low := fun k hk q hq => by
        obtain ⟨pk, hpk, -, -⟩ := idle_at hk
        exact low_atAll h L q₁ q₂ q₃ W.fence k
          (Nat.le_of_lt (List.getElem?_eq_some_iff.1 hpk).1) q hq
      kn := W.kn
      sealTie := W.sealTie
      behindTies := W.behindTies }

end

end P1L20

#print axioms P1L20.low_atAll
#print axioms P1L20.frame_kind_of4b
