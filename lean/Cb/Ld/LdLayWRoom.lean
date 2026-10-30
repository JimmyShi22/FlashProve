-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Ld/LdLayWRoom.lean: under the hypotheses of `Spec.ldLayW_room_ref`, the reference request with
one first sending does not always give up: room in every link, from room in a few.

Definitions, the statement (`Cb.Spec.ldLayW_room_ref`) and proofs: unfoldings, on
Cb/Ld/LdLayWGive.lean, Cb/Ld/LdLayWRef.lean and the parts' theorems on numbers. For all data: no
toy occurs here.

"Room at k" (Cb/Ld/LdLayWGive.lean): some verifier message of the link is withheld at no witness
with the core k; in Lean (`Link.RoomAt`, which `Spec.ldLayW_room_ref` concludes):
`∃ ρ : Rho l.R.shape, ∀ w x, A.rels.core w = k → ρ ∉ l.H.withheld w x`.
`H.withheld w x` is the union of two sets of verifier randomness that the honest side names:
`H.Bad`, which takes no argument, and `H.Hid w x`, which takes the witness and the explicit
statement. `A.core` is a map from the witnesses at a joint to a type K; the clause `keeps` of `Good`
asks that, for every w, x, coins c and ρ, `B.core` of the witness with which the honest prover ends
equals `A.core w`. `P.pBad` is a number of the structure `Nums`; the clause `prBad` of `Good` asks
that the probability of the set `H.Bad`, over the verifier's uniform randomness, is at most it.
`P.cov k` is a set of verifier randomness for each value k of the core; `Good` asks that, for every
w and x, in the relation or not, `H.Hid w x` lies in `P.cov (A.core w)` (`cover`), and that every
`P.cov k` has probability at most `P.pHid` (`prCov`). In this file `l.H.withheld` and `A.rels.core`
(`H.withheld`, `A.core` in the sentences above) stand in a conclusion, one unfolding down
(`Link.RoomAt`), and in premises (the three fields of `LdRefD.RoomD` are `Link.RoomAt` too); the
four clauses stand as premises: `IOR.GoodB` (Ior/Masked.lean) has them too, `roomQ` has `Link.GoodB`
as its premise, and `r.Hyp` gives it for every link.
A link with the bundle whose two probabilities are 0 has room. By the parts' theorems on numbers
that covers every sending, step, batching, split and location, the shifts, the front's sumchecks and
the batchings of tensor rows. What is left, and asked here, are the first three of the main names.

Main names:
  `A.RoomD k`, of a body A: the front's lookup's link; the range check's draw; the digits' lookup's
    link: each has room at k.
  `S.RoomD k`, of a closed segment S: `S.A.RoomD k`, and: the two probabilities of the closing's
    link from bridge to fold add up to less than 1.
  `L.RoomD k`: `S.RoomD k` of every segment S of the list L.
  `Spec.ldLayW_room_ref`: the reference request r with one first sending (`ldReqRef1`), `r.Hyp`,
    `L.RoomD k`, `T.A.RoomD k`: the request as one link has room at k.

Why: `roomQ k l`: "if l has all of the bundle but zero knowledge, it has room at k". It holds of a
link by its numbers alone where `l.P.pBad + l.P.pHid < 1` (`link_room_nums`); the three links of the
premise `A.RoomD k` have it from that premise. So it goes through the lists with no hypothesis that
a link has that bundle, under `L.RoomD k` and `T.A.RoomD k`; `r.Hyp` enters once, at the end (every
link has that bundle).

Limits: this file does not say that the links that are left have room: a masked block withholds
nothing (the item's field "free": `Honest.MM.free`, Ior/Masked.lean; for both lookups:
`Spec.ldLayW_roomD`, Cb/Ld/LdLayWRoomZk.lean, with the draw's room among its hypotheses); the draw
has room if some ternary matrix is outside the window event (`Spec.ldLayW_draw_room`,
Cb/Ld/LdLayWRef.lean); a closing's link: by its numbers (`link_room_nums`; a group's own:
`GPack.link_room`, Cb/Ld/LdLayWRoomZk.lean).

Terms: lean/GLOSSARY.md.
-/
import Cb.Ld.LdLayWRef

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop Blocks Cb.Ood IOR IOR.Chain Cb.Rng Cb.RngPk Cb.Lkp Cb.LdLkp
open scoped ENNReal

/-- "if the link has all of the bundle but zero knowledge, it has room at k" -/
abbrev roomQ {Kc : Type} (k : Kc) : ∀ A B : Joint Kc, Link Kc A B → Prop := fun _ _ l =>
  l.GoodB → l.RoomAt k

/-- modus ponens, link by link; "every link has the bundle without its clause on zero knowledge" in
the two forms -/
theorem each_room_mp {K : Type} (k : K) {A B : Joint K} (c : Chain K A B) :
    c.AllB → c.Each (roomQ k) → c.Each (fun _ _ l => l.RoomAt k) := by
  induction c with
  | one l => intro hB h; exact (each_one _ l).2 ((each_one _ l).1 h ((allB_one l).1 hB))
  | snoc c l ih => intro hB h; exact (each_snoc _ c l).2 ⟨ih ((allB_snoc c l).1 hB).1 ((each_snoc _ c l).1 h).1, ((each_snoc _ c l).1 h).2 ((allB_snoc c l).1 hB).2⟩

theorem link_room_nums {K : Type} (k : K) {A B : Joint K}
    (l : Link K A B) (h : l.P.pBad + l.P.pHid < 1) : roomQ k A B l :=
  fun g => ldLayW_room_nums K A B l k g h

theorem chain_room_nums {K : Type} (k : K) {A B : Joint K} (c : Chain K A B) :
    c.pBad + c.pHid < 1 → c.Each (roomQ k) := by
  induction c with
  | one l => intro h; rw [pBad_one, pHid_one] at h; exact (each_one _ l).2 (link_room_nums k l h)
  | snoc c l ih =>
      intro h
      rw [pBad_snoc, pHid_snoc] at h
      exact (each_snoc _ c l).2
        ⟨ih (lt_of_le_of_lt (add_le_add le_self_add le_self_add) h),
          link_room_nums k l (lt_of_le_of_lt (add_le_add le_add_self le_add_self) h)⟩

theorem chain_room_zero {K : Type} (k : K) {A B : Joint K} (c : Chain K A B)
    (h1 : c.pBad = 0) (h2 : c.pHid = 0) : c.Each (roomQ k) :=
  chain_room_nums k c (by rw [h1, h2, add_zero]; exact zero_lt_one)

section
variable {E Kc : Type} [Field E] [Fintype E]

theorem LdProg.room_nums (k : Kc) {a b : LdStage E Kc} (p : LdProg a b) :
    p.pBad + p.pHid < 1 → p.Each (roomQ k) := by
  induction p with
  | nil => intro _; exact (LdProg.each_nil _ _).2 trivial
  | snoc p m ih =>
      intro hn
      rw [LdProg.pBad_snoc, LdProg.pHid_snoc] at hn
      exact (LdProg.each_snoc _ p m).2
        ⟨ih (lt_of_le_of_lt (add_le_add le_self_add le_self_add) hn),
          chain_room_nums k m.chain (lt_of_le_of_lt (add_le_add le_add_self le_add_self) hn)⟩

theorem LdProg.room_zero (k : Kc) {a b : LdStage E Kc} (p : LdProg a b)
    (h1 : p.pBad = 0) (h2 : p.pHid = 0) : p.Each (roomQ k) :=
  p.room_nums k (by rw [h1, h2, add_zero]; exact zero_lt_one)

/-- a move that is neither a sub-protocol nor a closing's link -/
theorem LdMv.room_kind (k : Kc) {a b : LdStage E Kc} (m : LdMv a b)
    (hs : m.tag ≠ .sub) (hf : m.tag ≠ .fold) : m.chain.Each (roomQ k) := by
  obtain ⟨r1, r2, r3, r4, _, r6⟩ := ldSeg_rounds E Kc
  cases m with
  | send a d =>
    exact chain_room_zero k _ (by rw [LdMv.chain, pBad_one]; exact (r1 a d).2.2.1)
      (by rw [LdMv.chain, pHid_one]; exact (r1 a d).2.2.2)
  | sub a b c => exact absurd rfl hs
  | bat D =>
    exact chain_room_zero k _ (by rw [LdMv.chain, pBad_one]; exact (r2 D).2.1)
      (by rw [LdMv.chain, pHid_one]; exact (r2 D).2.2)
  | split D =>
    exact chain_room_zero k _ (by rw [LdMv.chain, pBad_one]; exact (r3 D).2.2.1)
      (by rw [LdMv.chain, pHid_one]; exact (r3 D).2.2.2)
  | fold D l => exact absurd rfl hf
  | loc D =>
    exact chain_room_zero k _ (by rw [LdMv.chain, pBad_one]; exact (r4 D).2.1)
      (by rw [LdMv.chain, pHid_one]; exact (r4 D).2.2)
  | step a b f g m back =>
    exact chain_room_zero k _ (r6 a b f g m back).2.2.1 (r6 a b f g m back).2.2.2

theorem LdMv.room_step (k : Kc) {a b : LdStage E Kc} (m : LdMv a b) (h : m.tag = .step) :
    m.chain.Each (roomQ k) :=
  m.room_kind k (fun e => LdTag.noConfusion (h.symm.trans e))
    (fun e => LdTag.noConfusion (h.symm.trans e))

theorem LdProg.room_kinds (k : Kc) {a b : LdStage E Kc} (p : LdProg a b) :
    (p.All fun t => t ≠ .sub ∧ t ≠ .fold) → p.Each (roomQ k) := by
  induction p with
  | nil => intro _; exact (LdProg.each_nil _ _).2 trivial
  | snoc p m ih =>
      intro ht
      obtain ⟨t1, t2⟩ := (LdProg.all_snoc _ _ _).1 ht
      exact (LdProg.each_snoc _ p m).2 ⟨ih t1, m.room_kind k t2.1 t2.2⟩

/-- a sub-protocol of one link -/
theorem room_sub_one (k : Kc) {a b : LdStage E Kc} (l : Link Kc a.J b.J) (h : roomQ k _ _ l) :
    (LdMv.sub a b (.one l)).chain.Each (roomQ k) := by
  rw [LdMv.chain]
  exact (each_one _ l).2 h

/-! ## The parts of a body -/

/-- read, then the range check -/
theorem LdRrD.room {E₀ : ExtSpec} {Wp : Type} (D : LdRrD E Kc E₀ Wp)
    (k : Kc) (hd : D.draw.RoomAt k) : D.prog.Each (roomQ k) := by
  unfold LdRrD.prog
  rw [LdProg.each_snoc, LdProg.each_snoc, LdProg.each_snoc, LdProg.each_snoc, LdProg.each_snoc]
  exact ⟨⟨⟨⟨⟨(LdProg.each_nil _ _).2 trivial, LdMv.room_step k _ rfl⟩,
          LdMv.room_kind k _ (fun e => LdTag.noConfusion e) (fun e => LdTag.noConfusion e)⟩,
        room_sub_one k D.draw fun _ => hd⟩,
      LdMv.room_step k _ rfl⟩,
    LdMv.room_kind k _ (fun e => LdTag.noConfusion e) (fun e => LdTag.noConfusion e)⟩

/-- the shift, and the digits' lookup -/
theorem LdDgP.room {E₀ : ExtSpec} {Wp : Type} (Q : LdDgP E Kc E₀ Wp)
    (mult : Q.X₄ × E → Ms Q.T E₀ → Prop) (ent : Ms Q.T E₀ → Q.Nn → E) (n : ℕ)
    (lk : Chain Kc (Q.lkS mult).J (Q.lkT ent n).J) (k : Kc) (hl : lk.Each (roomQ k)) :
    (Q.prog mult ent n lk).Each (roomQ k) := by
  unfold LdDgP.prog LdDgP.pre
  rw [LdProg.each_snoc, LdProg.each_snoc, LdProg.each_snoc, LdProg.each_snoc]
  refine ⟨⟨⟨⟨(LdProg.each_nil _ _).2 trivial, LdMv.room_step k _ rfl⟩,
        room_sub_one k Q.shift (link_room_nums k _ ?_)⟩,
      LdMv.room_step k _ rfl⟩,
    ?_⟩
  · show (0 : ℝ≥0∞) + 0 < 1
    rw [add_zero]; exact zero_lt_one
  · rw [LdMv.chain]
    exact hl

/-- the front's shift and lookup -/
theorem LdPreD.room {S : Sig E} {E₀ : ExtSpec} {Wp : Type} (F : LdPreD E Kc S E₀ Wp) (k : Kc)
    (hl : (F.s2.linkA F.jT F.lkBk).RoomAt k) : F.prog.Each (roomQ k) := by
  unfold LdPreD.prog
  rw [LdProg.each_snoc, LdProg.each_snoc, LdProg.each_snoc, LdProg.each_snoc]
  refine ⟨⟨⟨⟨(LdProg.each_nil _ _).2 trivial, room_sub_one k _ (link_room_nums k _ ?_)⟩,
        LdMv.room_step k _ rfl⟩,
      room_sub_one k _ fun _ => hl⟩,
    LdMv.room_step k _ rfl⟩
  show (0 : ℝ≥0∞) + 0 < 1
  rw [add_zero]; exact zero_lt_one

/-- the front -/
theorem LdFrontTab.room {z : LdStage E Kc} (B : LdFrontTab E Kc z)
    (k : Kc) (hp : B.pre.Each (roomQ k)) : B.prog.Each (roomQ k) := by
  unfold LdFrontTab.prog LdFrontTab.head
  rw [LdProg.each_snoc, ldLayW_app, LdProg.each_snoc, ldLayW_app]
  obtain ⟨-, i2, i3, -⟩ := ldSegFront_in_nums E Kc B.Z z.S z.E₀ z.Wp B.R0 B.msg0
  exact ⟨⟨⟨⟨hp, LdProg.room_zero k _ i2 i3⟩, LdMv.room_step k _ rfl⟩,
      LdProg.room_zero k _ (B.tw_nums B.m).2.1 (B.tw_nums B.m).2.2⟩,
    LdMv.room_step k _ rfl⟩

/-- a body -/
theorem LdBodyD.room {E₀ : ExtSpec} {Wp : Type} (Y : LdBodyD E Kc E₀ Wp) (z : LdStage E Kc)
    (tensor : LdProg Y.tgt z) (k : Kc) (hf : Y.front.Each (roomQ k)) (hd : Y.G.Q.D.draw.RoomAt k)
    (hl : Y.lk.Each (roomQ k)) (ht : tensor.Each (roomQ k)) :
    (Y.body z tensor).Each (roomQ k) := by
  unfold LdBodyD.body
  rw [ldLayW_app, LdProg.each_snoc, ldLayW_app, ldLayW_app]
  exact ⟨⟨⟨⟨hf, Y.G.Q.D.room k hd⟩, Y.G.Q.room _ _ _ _ k hl⟩, LdMv.room_step k _ rfl⟩, ht⟩


/-! ## Bodies, segments, the request -/

/-- What is asked of a body. -/
structure LdRefD.RoomD {I : LdRefIx E} (A : LdRefD E Kc I) (k : Kc) : Prop where
  lkF  : (A.V.Fp.s2.linkA A.V.Fp.jT A.V.Fp.lkBk).RoomAt k
  draw : A.Xa.Q.D.draw.RoomAt k
  lkD  : A.Xa.link.RoomAt k

theorem LdRefD.room_front {I : LdRefIx E} (A : LdRefD E Kc I) (k : Kc) (h : A.RoomD k) :
    A.V.prog.Each (roomQ k) :=
  A.V.tab.room k (A.V.Fp.room k h.lkF)

theorem LdRefD.room_lk {I : LdRefIx E} (A : LdRefD E Kc I) (k : Kc) (h : A.RoomD k) :
    A.Xa.lk.Each (roomQ k) :=
  (each_one _ A.Xa.link).2 fun _ => h.lkD

theorem LdTenD.room (X : LdTenD E Kc) (St₁ : Type) (fz : X.bt.par.Mid → St₁)
    (Az : Rels Kc St₁ X.C.E0 (X.S.Msg × (X.C.PIdx × X.Wp))) (k : Kc) :
    (X.prog St₁ fz Az).Each (roomQ k) :=
  LdProg.room_zero k _ (ldSegRef_tn_nums E Kc X St₁ fz Az).2.1
    (ldSegRef_tn_nums E Kc X St₁ fz Az).2.2

theorem LdRefD.room {I : LdRefIx E} (A : LdRefD E Kc I) (St₁ : Type) (fz : A.X.bt.par.Mid → St₁)
    (Az : Rels Kc St₁ I.C.E0 (A.Xa.Q.T.Msg × (I.C.PIdx × (A.W₁ × A.Gh)))) (k : Kc) (h : A.RoomD k) :
    (A.body St₁ fz Az).Each (roomQ k) :=
  A.Y.room _ _ k (A.room_front k h) h.draw (A.room_lk k h) (A.X.room St₁ fz Az k)

/-- What is asked of a closed segment. -/
structure LdRefS.RoomD {I : LdRefIx E} {a : LdStage E Kc} (S : LdRefS E Kc I a) (k : Kc) :
    Prop where
  body : S.A.RoomD k
  fold : S.l.P.pBad + S.l.P.pHid < 1

theorem LdRefS.room {I : LdRefIx E} {a : LdStage E Kc} (S : LdRefS E Kc I a)
    (k : Kc) (h : S.RoomD k) : S.seg.Each (roomQ k) := by
  obtain ⟨r1, _, _, _, _, _⟩ := ldSeg_rounds E Kc
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · show (((LdProg.nil a).snoc S.entry).app (S.A.body S.K.St₁ S.K.fz S.K.Az)).Each (roomQ k)
    rw [ldLayW_app, LdProg.each_snoc]
    exact ⟨⟨(LdProg.each_nil _ _).2 trivial, LdMv.room_step k _ rfl⟩, S.A.room _ _ _ k h.body⟩
  · exact LdProg.room_kinds k _
      (LdProg.all_mono _ _
        (by
          rintro t (rfl | rfl | rfl)
            <;> exact ⟨fun e => LdTag.noConfusion e, fun e => LdTag.noConfusion e⟩)
        _ S.seg.batT)
  · show ((LdProg.nil _).snoc (.fold S.K.R.c1.fold S.l)).Each (roomQ k)
    rw [LdProg.each_snoc, LdMv.chain, each_one]
    exact ⟨(LdProg.each_nil _ _).2 trivial, link_room_nums k _ h.fold⟩
  · exact link_room_nums k _
      (by rw [(r1 _ S.seg.snd).2.2.1, (r1 _ S.seg.snd).2.2.2, add_zero]; exact zero_lt_one)
  · exact LdProg.room_kinds k _
      (LdProg.all_mono _ _
        (by
          rintro t (rfl | rfl)
            <;> exact ⟨fun e => LdTag.noConfusion e, fun e => LdTag.noConfusion e⟩)
        _ S.seg.locT)

def LdRefL.RoomD {I : LdRefIx E} {a : LdStage E Kc} (k : Kc) :
    {b : LdStage E Kc} → LdRefL E Kc I a b → Prop
  | _, .nil => True
  | _, .snoc L S => L.RoomD k ∧ S.RoomD k

theorem LdRefL.room {I : LdRefIx E} {a : LdStage E Kc} (k : Kc)
    {b : LdStage E Kc} (L : LdRefL E Kc I a b) :
    L.RoomD k → L.segs.Each (roomQ k) := by
  induction L with
  | nil => intro _; rw [LdRefL.segs]; exact (LdSegs.each_nil _ _).2 trivial
  | snoc L S ih => intro h; rw [LdRefL.RoomD] at h; rw [LdRefL.segs]; exact (LdSegs.each_snoc _ _ _).2 ⟨ih h.1, S.room k h.2⟩

end

section
variable {F E Kc : Type} [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E]

theorem LdRefT.room {R : LdORE F E Kc} {b : LdStage E Kc} (T : LdRefT R b)
    (k : Kc) (h : T.A.RoomD k) : T.tail.Each (roomQ k) := by
  unfold LdRefT.tail
  rw [LdProg.each_snoc, ldLayW_app, LdProg.each_snoc]
  exact ⟨⟨⟨(LdProg.each_nil _ _).2 trivial, LdMv.room_step k _ rfl⟩, T.A.room _ _ _ k h⟩,
    LdMv.room_step k _ rfl⟩

theorem LdORE.room_last (R : LdORE F E Kc) (k : Kc) : R.lastP.Each (roomQ k) := by
  unfold LdORE.lastP
  rw [LdProg.each_snoc, LdProg.each_snoc, LdProg.each_snoc]
  refine ⟨⟨⟨(LdProg.each_nil _ _).2 trivial, LdMv.room_step k _ rfl⟩,
      room_sub_one k R.X.link (link_room_nums k _ ?_)⟩,
    LdMv.room_step k _ rfl⟩
  show ((0 : ℝ≥0∞) + 0) + (0 + 0) < 1
  simp

end

/-- Under the three hypotheses below: the reference request with one first sending, as one link, has
room at k. -/
def Spec.ldLayW_room_ref : Prop :=
  ∀ (F E Kc : Type) [Field F] [Fintype F] [Field E] [Fintype E] [Algebra F E] (R : LdORE F E Kc)
      (a : LdStage E Kc) (first : LdSendD a) (b : LdStage E Kc) (L : LdRefL E Kc R.ix first.tgt b)
      (T : LdRefT R b) (d : a.J.W) (k : Kc),
    (ldReqRef1 R first b L T).Hyp → L.RoomD k → T.A.RoomD k →
    ((ldReqRef1 R first b L T).chain.link d).RoomAt k

theorem ldLayW_room_ref : Spec.ldLayW_room_ref := by
  intro F E Kc _ _ _ _ _ R a first b L T d k hH hL hT
  obtain ⟨r1, _, _, _, _, _⟩ := ldSeg_rounds E Kc
  refine ldLayW_room Kc _ _ _ d k (LdReq.chain_allB _ hH)
    (each_room_mp k _ (LdReq.chain_allB _ hH) ((ldLayW_req E Kc _ _ _ _).2 ⟨?_, ?_, ?_, ?_⟩))
  · exact link_room_nums k first.link
      (by rw [(r1 _ first).2.2.1, (r1 _ first).2.2.2, add_zero]; exact zero_lt_one)
  · exact (LdProg.each_nil _ _).2 trivial
  · exact L.room k hL
  · show (T.tail.app R.lastP).asSub.Each (roomQ k)
    rw [LdProg.each_asSub, ldLayW_app]
    exact ⟨T.room k hT, R.room_last k⟩

end Cb
