-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/TypedOracleCompiler/Tagged.lean: the library's wire records, with the library's tagged body of a leaf, are
an instance of the second form of the compiler's verifier side.

This file belongs to the second form of the verifier's side of the library's compiler under
OnBytes/TypedOracleCompiler/ (namespace `TypedOracleCompiler`). What that form is, and in which five respects it differs
from the library's own, is told in the head of OnBytes/TypedOracleCompiler/Iop/BatchWire.lean. The folder has the
verifier's side alone: no prover and no completeness. Nothing here is on hiding. The library has no
file of this name.

  `tagged L`
      The library's interface L with the library's own body of a leaf (a symbol of an encoded index,
      or of a prover oracle with protocol and position, or padding), and with local rounds alone in
      Test and Link.
  `prjSym`, `prjSym_emb`
      The library's reading of such a body (Compile/Batch/Sound.lean), to the letter but for three
      names (shapeOf → shape0, Body → Body0, L made explicit).
  `ofRB`, `ofSB`, `ofQB`, `ofB`
      A wire of the library as a wire of this form: a component has its one tree, or none; the three
      request trees have the library's one depth.
  `ofB_okg`
      A lawful wire of the library gives a lawful wire of this form.
  `bcsAt_ofB`
      This form's theorem at a lawful wire of the library, under its other hypotheses.

So the laws of this form's wires (`OKG`) are met wherever the library's are, and this form's
theorems hold at `ofB W`, of this form's verifier, for every lawful wire W of the library, under
their other hypotheses. (Under this namespace `Iop.BatchProtocolWithLeafBody`, `Iop.QueryLayout`, `Compile.Batch.BcsAt` mean
this form's; the library's are written with `_root_`.)

Limits. Not here: that this form's verifier at `ofB W` and the library's at W accept the same
strings (they ask different families of oracles); a lawful wire with two trees in a component.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.TypedOracleCompiler.Compile.Batch.Sound
import Iop.BatchWire

namespace TypedOracleCompiler.Tagged
open _root_.Compile Rom Prob
open _root_.Iop (Shape Round RAnn RoundSplits OPos OSym ExtSpec BatchInteractiveOracleProof Dig)

variable {I X : Type}

/-- the shape of a protocol of the library's interface -/
def shape0 (L : _root_.Iop.BatchProtocol I X) : Tag → Shape
  | .test => L.offline.shape
  | .link => L.link.shape
  | .onl => L.onlineBatch.loc.shape

/-- the library's body of a leaf -/
abbrev Body0 (L : _root_.Iop.BatchProtocol I X) : Type := Option (L.Symbol ⊕ (Σ t : Tag, SymAny (shape0 L t)))

/-- the library's interface with the library's body, and with local rounds alone in Test and Link -/
def tagged (L : _root_.Iop.BatchProtocol I X) : Iop.BatchProtocolWithLeafBody I X :=
  { L with Bd := Body0 L, annT := RoundSplits.allLocal L.offline.shape, annL := RoundSplits.allLocal L.link.shape }

open Classical in
/-- read the body of a leaf as the symbol at position p of a prover oracle of the protocol t -/
noncomputable def prjSym {L : _root_.Iop.BatchProtocol I X} (t : Tag) (p : OPos (shape0 L t)) :
    Body0 L → Option (OSym (shape0 L t) p)
  | some (.inr ⟨t', z⟩) =>
      if h : t' = t then
        if h2 : (h ▸ z : SymAny (shape0 L t)).1 = p then
          some (h2 ▸ (h ▸ z : SymAny (shape0 L t)).2)
        else none
      else none
  | _ => none

theorem prjSym_emb {L : _root_.Iop.BatchProtocol I X} (t : Tag) (p : OPos (shape0 L t))
    (a : OSym (shape0 L t) p) :
    prjSym t p (some (.inr ⟨t, (⟨p, a⟩ : SymAny (shape0 L t))⟩)) = some a := by
  simp [prjSym]

/-! ## A wire of the library as a wire of this form -/

def ofGr {C P : Type} (g : _root_.Iop.GrW C P) : Iop.GrW C P :=
  ⟨g.b, g.tst, g.set, g.more, g.put, g.get⟩

theorem ofGr_ok {C P : Type} {g : _root_.Iop.GrW C P} (h : g.OK) : (ofGr g).OK :=
  ⟨h.tst_set, h.set_tst, h.set_set, h.get_put⟩

/-- one round: each component has its one tree, or none -/
def ofRB {lam K : ℕ} {r : Round} {a : RAnn r} (w : _root_.Iop.WireRB lam K r a) :
    Iop.WireRB lam K r a where
  pt := w.pt
  depth0 := if w.has0 then [w.depth0] else []
  depthJ := if w.hasJ then [w.depthJ] else []
  tree := fun _ => 0
  place := w.place
  posAt0 := fun k j => if k = 0 then w.posAt0 j else none
  posAtJ := fun k j => if k = 0 then w.posAtJ j else none
  chal := w.chal
  pr0 := w.pr0
  prJ := w.prJ
  gr0 := w.gr0.map ofGr
  grJ := w.grJ.map ofGr

theorem ofRB_okg {lam K : ℕ} {r : Round} {a : RAnn r} {w : _root_.Iop.WireRB lam K r a}
    (h : w.OKG) : (ofRB w).OKG where
  place_lt0 := fun p hp => by
    have h1 : w.has0 = true := by
      by_contra hn
      have := h.no0 (by simpa using hn) (w.place p)
      rw [h.posAt0_place p hp] at this
      cases this
    exact ⟨w.depth0, by simp [ofRB, h1], h.place_lt0 p hp⟩
  place_ltJ := fun p hp => by
    have h1 : w.hasJ = true := by
      by_contra hn
      have := h.noJ (by simpa using hn) (w.place p)
      rw [h.posAtJ_place p hp] at this
      cases this
    exact ⟨w.depthJ, by simp [ofRB, h1], h.place_ltJ p hp⟩
  posAt0_place := fun p hp => by simpa [ofRB] using h.posAt0_place p hp
  posAtJ_place := fun p hp => by simpa [ofRB] using h.posAtJ_place p hp
  place_posAt0 := fun k j p hp => by
    by_cases hk : k = 0
    · subst hk
      have := h.place_posAt0 j p (by simpa [ofRB] using hp)
      exact ⟨this.1, rfl, this.2⟩
    · simp [ofRB, hk] at hp
  place_posAtJ := fun k j p hp => by
    by_cases hk : k = 0
    · subst hk
      have := h.place_posAtJ j p (by simpa [ofRB] using hp)
      exact ⟨this.1, rfl, this.2⟩
    · simp [ofRB, hk] at hp
  no0 := fun k hk j => by
    by_cases h0 : k = 0
    · subst h0
      cases h1 : w.has0 with
      | true => simp [ofRB, h1] at hk
      | false => simpa [ofRB] using h.no0 h1 j
    · simp [ofRB, h0]
  noJ := fun k hk j => by
    by_cases h0 : k = 0
    · subst h0
      cases h1 : w.hasJ with
      | true => simp [ofRB, h1] at hk
      | false => simpa [ofRB] using h.noJ h1 j
    · simp [ofRB, h0]
  chal_unif := h.chal_unif
  gr0_ok := fun g e => by
    obtain ⟨g', hg, rfl⟩ := Option.map_eq_some_iff.1 e
    exact ofGr_ok (h.gr0_ok g' hg)
  grJ_ok := fun g e => by
    obtain ⟨g', hg, rfl⟩ := Option.map_eq_some_iff.1 e
    exact ofGr_ok (h.grJ_ok g' hg)

def ofSB {lam K : ℕ} : (s : Shape) → (A : RoundSplits s) → _root_.Iop.RoundsQueryLayout lam K s A →
    Iop.RoundsQueryLayout lam K s A
  | [], _, _ => ()
  | _ :: s, (_, A), (w, W) => (ofRB w, ofSB s A W)

theorem ofSB_okg {lam K : ℕ} :
    ∀ (s : Shape) (A : RoundSplits s) (W : _root_.Iop.RoundsQueryLayout lam K s A),
      _root_.Iop.RoundsQueryLayout.OKG s A W → Iop.RoundsQueryLayout.OKG s A (ofSB s A W)
  | [], _, _, _ => trivial
  | _ :: s, (_, A), (_, W), h => ⟨ofRB_okg h.1, ofSB_okg s A W h.2⟩

theorem ofSB_depthLe {lam K : ℕ} (d : ℕ) :
    ∀ (s : Shape) (A : RoundSplits s) (W : _root_.Iop.RoundsQueryLayout lam K s A),
      _root_.Iop.RoundsQueryLayout.DepthLe d s A W → Iop.RoundsQueryLayout.DepthLe d s A (ofSB s A W)
  | [], _, _, _ => trivial
  | _ :: s, (_, A), (w, W), h =>
    ⟨⟨fun e he => by
        cases h1 : w.has0 <;> simp [ofRB, h1] at he
        subst he; exact h.1.1,
      fun e he => by
        cases h1 : w.hasJ <;> simp [ofRB, h1] at he
        subst he; exact h.1.2⟩, ofSB_depthLe d s A W h.2⟩

def ofQB {lam K : ℕ} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}
    (wq : _root_.Iop.ProtocolQueryLayout lam K Q) :
    Iop.ProtocolQueryLayout lam K Q :=
  ⟨ofSB _ _ wq.sh, wq.ext, wq.decO, wq.nOpen, wq.maxDepth⟩

theorem ofQB_okg {lam K : ℕ} {Y : Type} {E : ExtSpec} {Q : BatchInteractiveOracleProof Y E}
    {wq : _root_.Iop.ProtocolQueryLayout lam K Q} (h : wq.OKG) : (ofQB wq).OKG :=
  ⟨ofSB_okg _ _ _ h.sh, h.ext, h.opens, ofSB_depthLe _ _ _ _ h.depth⟩

/-- a wire of the library, with the library's way of writing symbols into bodies -/
noncomputable def ofB {lam : ℕ} {L : _root_.Iop.BatchProtocol I X} (W : _root_.Iop.QueryLayout lam L) :
    Iop.QueryLayout lam (tagged L) where
  K := W.K
  T := ofQB W.T
  Lk := ofQB W.Lk
  B := ofQB W.B
  depth := W.depth
  depthReq := W.depthReq
  depthReqT := W.depthReq
  depthReqL := W.depthReq
  embE := fun s => (some (.inl s) : Body0 L)
  prjE := fun (b : Body0 L) => match b with
    | some (.inl s) => some s
    | _ => none
  embT := fun p a => (some (.inr ⟨Tag.test, ⟨p, a⟩⟩) : Body0 L)
  prjT := prjSym (L := L) Tag.test
  embL := fun p a => (some (.inr ⟨Tag.link, ⟨p, a⟩⟩) : Body0 L)
  prjL := prjSym (L := L) Tag.link
  embB := fun p a => (some (.inr ⟨Tag.onl, ⟨p, a⟩⟩) : Body0 L)
  prjB := prjSym (L := L) Tag.onl

theorem ofB_okg {lam : ℕ} {L : _root_.Iop.BatchProtocol I X} {W : _root_.Iop.QueryLayout lam L} (h : W.OKG) :
    (ofB W).OKG where
  T := ofQB_okg h.T
  Lk := ofQB_okg h.Lk
  B := ofQB_okg h.B
  fits := h.fits
  slots := h.slots
  extDepth := h.extDepth
  depthT := h.depthT
  depthL := h.depthL
  depthB := h.depthB
  extT := h.extT
  extB := h.extB
  extL := h.extL
  prjE_emb := fun _ => rfl
  prjT_emb := fun p a => prjSym_emb (L := L) Tag.test p a
  prjL_emb := fun p a => prjSym_emb (L := L) Tag.link p a
  prjB_emb := fun p a => prjSym_emb (L := L) Tag.onl p a

/-- This form's theorem at a lawful wire of the library, under its other hypotheses. -/
theorem bcsAt_ofB {lam : ℕ} {L : _root_.Iop.BatchProtocol I X} {W : _root_.Iop.QueryLayout lam L}
    {Rno : I → X → Prop} {εs : ENNReal} (hS : L.Sound Rno εs) (hT : L.offline.IsLocal)
    (hL : L.link.IsLocal) (hB : L.onlineBatch.loc.IsLocal) (hco : L.onlineBatch.ann.Coherent) (hW : W.OKG) :
    Compile.Batch.BcsAt (ofB W) Rno εs :=
  Compile.Batch.bcsSoundBatchG I X lam (tagged L) (ofB W) Rno εs hS hT hL hB hco
      (ofB_okg hW) rfl rfl

end TypedOracleCompiler.Tagged
