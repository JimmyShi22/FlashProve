-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Obj/LdObjectCtbReq.lean: bookkeeping for the compiler to a random-oracle argument, for which it
is asked that the types of positions, symbols and plain messages of every round are countable: here
for the reduction in front of the test on a batch, given as a list of steps.

Definitions, theorems. Bookkeeping for the passage to one random oracle, as Cb/Obj/LdObjectCtb.lean
(which says what `CtbSh`, CompileK/ImplCountable.lean, is) and Cb/Obj/LdObjectCtbPre.lean.

Main names:
  `m.Ctb`: what is asked of a move (`LdMv`, Cb/Req1/LdSeg.lean): a sending: the symbols of the
    family sent are countable (`Sig.CtbSy`); a sub-protocol: every link of its chain is countable; a
    fold: its link is; batching, split, locations, a step without rounds: nothing.
  `ctb_mv`: then every link of the move is countable.
  `p.Ctb`, `ctb_prog`, `ctb_prog_free`: a list of moves; a list that holds no sending, no
    sub-protocol and no fold is countable as it stands.
  `s.Ctb`, `ctb_seg`, `ctb_seg_link`: a segment: asked of its body, its folds and its one sending
    only (the parts "batching" and "locations" are free by the kinds of their moves); `ctb_seg`
    also: the chain in front is countable (`c₀.Ctb`).
  `S.Ctb`, `ctb_segs`; `r.Ctb`, `ctb_req`, `ctb_req_link`: segments in a row; a request: the shape
    of the whole chain as one link.

Limits: on a protocol this file has one kind of conclusion, countability (as in `ctb_seg`,
`ctb_req`, `ctb_req_link`); beyond it no statement of the file concludes anything of a protocol.

Terms: lean/GLOSSARY.md.
-/
import Cb.Obj.LdObjectCtbPre
import Cb.Req1.LdReq

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

section
variable {E Kc : Type} [Field E] [Fintype E]

/-- What is asked of a move. -/
def LdMv.Ctb : {a b : LdStage E Kc} → LdMv a b → Prop
  | _, _, .send _ d => d.N.CtbSy
  | _, _, .sub _ _ c => c.Ctb
  | _, _, .bat _ => True
  | _, _, .split _ => True
  | _, _, .fold _ l => l.Ctb
  | _, _, .loc _ => True
  | _, _, .step _ _ _ _ _ _ => True

theorem ctb_send {a : LdStage E Kc} (d : LdSendD a) (h : d.N.CtbSy) : d.link.Ctb :=
  ctb_sendFam d.N d.Sd (a.St × a.S.Smp) (a.E₀.prod a.S.ext) h

theorem ctb_mv : ∀ {a b : LdStage E Kc} (m : LdMv a b), m.Ctb → m.chain.Ctb
  | _, _, .send _ d, h => (Chain.ctb_one _).2 (ctb_send d h)
  | _, _, .sub _ _ _, h => h
  | _, _, .bat D, _ => (Chain.ctb_one _).2 (ctb_drawR D.Z.D _ _)
  | _, _, .split _, _ =>
    (Chain.ctb_one _).2
      ⟨⟨inferInstanceAs (Countable Empty), fun p => p.elim, inferInstanceAs (Countable E)⟩, trivial⟩
  | _, _, .fold _ _, h => (Chain.ctb_one _).2 h
  | _, _, .loc D, _ => (Chain.ctb_one _).2 (ctb_plain Unit (Fin D.t → D.P) () trivial)
  | _, _, .step _ _ _ _ _ _, _ => (Chain.ctb_one _).2 trivial

/-- a list of moves -/
def LdProg.Ctb : {a b : LdStage E Kc} → LdProg a b → Prop
  | _, _, .nil _ => True
  | _, _, .snoc p m => p.Ctb ∧ m.Ctb

theorem LdProg.ctb_snoc {a b c : LdStage E Kc} (p : LdProg a b) (m : LdMv b c) :
    (p.snoc m).Ctb ↔ p.Ctb ∧ m.Ctb := by rw [LdProg.Ctb]
theorem LdProg.ctb_nil (a : LdStage E Kc) : (LdProg.nil a).Ctb := by rw [LdProg.Ctb]; trivial

theorem ctb_prog {A : Joint Kc} {a b : LdStage E Kc} (c : Chain Kc A a.J) (p : LdProg a b)
    (hc : c.Ctb) (h : p.Ctb) : (p.onto c).Ctb := by
  induction p with
  | nil =>
    rw [LdProg.onto]
    exact hc
  | snoc p m ih =>
    rw [LdProg.onto]
    exact chainCtb_append _ _ (ih ((LdProg.ctb_snoc p m).1 h).1)
      (ctb_mv m ((LdProg.ctb_snoc p m).1 h).2)

/-- a move that is no sending, no sub-protocol and no fold asks nothing -/
theorem ctb_mv_free :
    ∀ {a b : LdStage E Kc} (m : LdMv a b), m.tag ≠ .send → m.tag ≠ .sub → m.tag ≠ .fold → m.Ctb
  | _, _, .send _ _, h, _, _ => absurd rfl h
  | _, _, .sub _ _ _, _, h, _ => absurd rfl h
  | _, _, .bat _, _, _, _ => trivial
  | _, _, .split _, _, _, _ => trivial
  | _, _, .fold _ _, _, _, h => absurd rfl h
  | _, _, .loc _, _, _, _ => trivial
  | _, _, .step _ _ _ _ _ _, _, _, _ => trivial

theorem ctb_prog_free (q : LdTag → Prop) (hq : ∀ t, q t → t ≠ .send ∧ t ≠ .sub ∧ t ≠ .fold)
    {a b : LdStage E Kc} (p : LdProg a b) (h : p.All q) : p.Ctb := by
  induction p with
  | nil => exact LdProg.ctb_nil _
  | snoc p m ih =>
    rw [LdProg.All] at h
    exact (LdProg.ctb_snoc p m).2 ⟨ih h.1, ctb_mv_free m (hq _ h.2).1 (hq _ h.2).2.1 (hq _ h.2).2.2⟩

/-- What is asked of a segment. -/
structure LdSeg.Ctb {a d : LdStage E Kc} (s : LdSeg a d) : Prop where
  body : s.body.Ctb
  fold : s.fold.Ctb
  snd  : s.snd.N.CtbSy

theorem ctb_seg {A : Joint Kc} {a d : LdStage E Kc} (c₀ : Chain Kc A a.J) (s : LdSeg a d)
    (hc : c₀.Ctb) (h : s.Ctb) : (s.onto c₀).Ctb := by
  have hb : s.bat.Ctb :=
    ctb_prog_free _
      (fun t ht => by rcases ht with rfl | rfl | rfl <;> exact ⟨nofun, nofun, nofun⟩) s.bat s.batT
  have hl : s.loc.Ctb :=
    ctb_prog_free _
      (fun t ht => by rcases ht with rfl | rfl <;> exact ⟨nofun, nofun, nofun⟩) s.loc s.locT
  exact ctb_prog _ s.loc
    ((Chain.ctb_snoc _ _).2
      ⟨ctb_prog _ s.fold (ctb_prog _ s.bat (ctb_prog c₀ s.body hc h.body) hb) h.fold,
        ctb_send s.snd h.snd⟩) hl

theorem ctb_seg_link {a d : LdStage E Kc} (s : LdSeg a d) (w₀ : a.W) (h : s.Ctb) :
    CtbSh (s.chain.link w₀).R.shape :=
  chainCtb_link _ _ (ctb_seg _ s ((Chain.ctb_one _).2 trivial) h)

/-- segments in a row -/
def LdSegs.Ctb : {a b : LdStage E Kc} → LdSegs a b → Prop
  | _, _, .nil _ => True
  | _, _, .snoc S s => S.Ctb ∧ s.Ctb

theorem LdSegs.ctb_snoc {a b c : LdStage E Kc} (S : LdSegs a b) (s : LdSeg b c) :
    (S.snoc s).Ctb ↔ S.Ctb ∧ s.Ctb := by rw [LdSegs.Ctb]

theorem ctb_segs {A : Joint Kc} {a b : LdStage E Kc} (c : Chain Kc A a.J) (S : LdSegs a b)
    (hc : c.Ctb) (h : S.Ctb) : (S.onto c).Ctb := by
  induction S with
  | nil =>
    rw [LdSegs.onto]
    exact hc
  | snoc S s ih =>
    rw [LdSegs.onto]
    exact ctb_seg _ s (ih ((LdSegs.ctb_snoc S s).1 h).1) ((LdSegs.ctb_snoc S s).1 h).2

/-- What is asked of a request. -/
structure LdReq.Ctb {a z : LdStage E Kc} (r : LdReq a z) : Prop where
  first : r.first.N.CtbSy
  more  : r.more.Ctb
  segs  : r.segs.Ctb
  last  : r.last.Ctb

theorem ctb_req {a z : LdStage E Kc} (r : LdReq a z) (h : r.Ctb) : r.chain.Ctb :=
  ctb_prog _ r.last
    (ctb_segs _ r.segs
      (ctb_prog _ r.more ((Chain.ctb_one _).2 (ctb_send r.first h.first)) h.more) h.segs) h.last

/-- The shape of a request as one link. -/
theorem ctb_req_link {a z : LdStage E Kc} (r : LdReq a z) (w₀ : a.W) (h : r.Ctb) :
    CtbSh (r.chain.link w₀).R.shape :=
  chainCtb_link _ _ (ctb_req r h)

omit [Fintype E] in
/-- a block at the base, lifted over the oracle messages of a stage -/
theorem ctb_lift (a : LdStage E Kc) {St' Wp' : Type} {E₀' : ExtSpec}
    (B : Rels Kc St' E₀' (a.S.Msg × Wp')) (R : IOR a.St a.E₀ St' E₀')
    (H : R.Honest (a.S.Msg × a.Wp) (a.S.Msg × Wp'))
    (ext : a.S.Msg → a.St × a.E₀.Str → Tr R.shape → Wp' → a.Wp)
    (P : Nums Kc R) (h : CtbSh R.shape) : (a.lift B R H ext P).Ctb := h

end
end Cb
