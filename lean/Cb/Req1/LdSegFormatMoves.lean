-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Cb/Req1/LdSegFormatMoves.lean: each named move of a preamble has a format, under the
hypotheses of its statement.

Definitions, statements (in `Cb.Spec`) and proofs. The notions: Cb/Req1/LdReqFormat.lean (`IdxLink`,
`Passes`, `Hands`, `Bears`: `Link.Fmt`), Cb/Req1/LdSegFormat.lean (the format of a stage,
`a.fmt i rc px q`; q is the demand); the rules: Cb/Req1/LdSegFormatKit.lean.
Book-keeping in the sense of Cb/Req1/LdReqFormat.lean.

The encoded index is among the further oracles E₀ of a stage, at a place i. While a test is open the
further oracles are (the open word, the old ones), and the index is at `i.inr`. The record is read
off that part St₀ of the explicit part which no named move touches (of the fold's link l it is asked
that it keeps the record: `Spec.ldFmt_fold`; so of a step and of a sub-protocol: `Spec.ldFmt_step`,
`Spec.ldFmt_mv`); the prover encoded index off the further witness.

Main names:
  `Spec.ldFmt_send`: one sending. Place, record: unchanged. Asked: what is read off the new further
    witness of the sender's rest is what was read off the old one (px' (D.rest w).2 = px w.2). The
    demand after it: the old demand on the old oracles, and at most t a long positions of each new
    member (`Sig.qSum`); `Bears` is the sending's own (Cb/Ld/LdSendPiece.lean), from `d.Hyp`.
  `Spec.ldFmt_bat`: many rows into one: the verifier draws; oracles, witness, demand unchanged.
    Nothing is asked beside whatever the arguments hold as proofs.
  `Spec.ldFmt_split`: a row on two groups into a row on each: the prover says one scalar; the same.
    Nothing is asked beside whatever the arguments hold as proofs.
  `Spec.ldFmt_fold`: bridge, arrangement, fold. Asked: the link l has the format up to the joint
    `D.mid` (`D.fmtMid`: the index beside the folded word), and the demand at `D.mid` is met by the
    sources, under the re-bracketing `D.pE`, of a set within the demand after the move. After it the
    index is at `i.inr`.
  `Spec.ldFmt_loc`: the locations. The verifier reads the open word only. The index comes back from
    `i.inr` to i. Asked: the demand before the move is met by what the move needs (its budget asks
    nothing: it sends no oracle).
  `Spec.ldFmt_loc_need`: see its docstring.
  `Spec.ldFmt_step`: a step without rounds. Asked: its map of oracles moves the index from `φ.ix` to
    `ψ.ix` (`ExtMap.Moves`), its map of explicit parts keeps the record, the honest prover's map
    keeps the prover encoded index, and the demand before it is met by the sources of a set within
    the demand after it.
  `Spec.ldFmt_lift`: a reduction on claims about the messages, lifted over the oracle messages of a
    stage (`a.lift`): `IdxLink` and `Passes` from those of the reduction on the further oracles.
  `Spec.ldFmt_mv`: for send, bat, split, fold and loc the format of the link as a statement on the
    move (`LdMv.Fmt`); for "sub" the format of its chain is the hypothesis itself.

Limits: "Nothing hidden is withheld" is asked nowhere in this file. `H.withheld w x` is the union
of two sets of
verifier randomness that the honest side names: `H.Bad`, which takes no argument, and `H.Hid w x`,
which takes the witness and the explicit statement. This file does not say that the demands can be
met together along a whole request (numbers of positions against what the encodings bear): that is
a matter of an instance. This file says nothing on `Hands` of a lifted reduction.

Terms: lean/GLOSSARY.md.
-/
import Cb.Req1.LdSegFormat
import Cb.Req1.LdSegFormatKit
import Cb.Ld.LdSendPiece

set_option autoImplicit false

namespace Cb
open Iop Prob Hiop IOR

/-! ## The blocks -/

section Blocks
variable {E : Type} [Field E] {E0 : ExtSpec}

/-- the sending of a family leaves every oracle of its input alone -/
theorem ldSendFam_idx (N : Sig E) (Sd : N.Seeds) (X : Type) (Ex : ExtSpec) (j : IxAt E0 Ex) :
    (ldSendFam N Sd X Ex).IdxLink j (j.inl N.ext) := by
  refine ⟨fun _ _ hp => absurd hp (Finset.notMem_empty _),
    fun _ _ _ hq => absurd hq (Finset.notMem_empty _),
    fun _ _ => rfl,
    fun _ _ => ⟨rfl, rfl⟩,
    fun _ q hq p hp => ?_⟩
  cases q with
  | inl q => exact hq p (congrArg Sum.inl (Finset.mem_singleton.1 hp).symm)
  | inr q => exact absurd hp (Finset.notMem_empty _)

omit [Field E] in
/-- the renaming after a sending moves what is among the further oracles -/
theorem mergeE_moves (S N : Sig E) (E₀ : ExtSpec) (i : IxAt E0 E₀) :
    (S.mergeE N E₀).Moves ((i.inl S.ext).inl N.ext) (i.inl (S.sum N).ext) := by
  refine ⟨fun _ => rfl, fun _ => rfl, fun q hq p hp => ?_⟩
  rcases q with q | ⟨a | a, x⟩
  · exact hq p (congrArg Sum.inl (Sum.inl.inj (Sum.inl.inj (Finset.mem_singleton.1 hp))).symm)
  · cases Sum.inl.inj (Finset.mem_singleton.1 hp)
  · cases Finset.mem_singleton.1 hp

theorem ldSay_copies {X X' Pl : Type} (d : Pl) (nx : X → Pl → X') (Ex : ExtSpec) :
    (ldSay d nx Ex).OnlyCopies :=
  ⟨fun _ => rfl, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩⟩

omit [Field E] in
/-- the block "locations" leaves the oracles beside the open word alone -/
theorem ldLocOf_idx {P Xi Xo : Type} [Fintype P] [Nonempty P] (V : LdLocV E P Xi Xo)
    (F : ExtSpec) (j : IxAt E0 F) :
    (ldLocOf V F).IdxLink (j.inr V.Cin.ext) (j.inr extNone) := by
  classical
  refine ⟨fun ρ p hp => ?_, fun _ _ _ hq => absurd hq (Finset.notMem_empty _), fun _ _ => rfl,
    fun _ _ => ⟨rfl, rfl⟩, fun _ q hq p hp => ?_⟩
  · obtain ⟨_, _, h⟩ := Finset.mem_image.1 hp
    cases h
  · cases q with
    | inl q => exact q.elim
    | inr q => exact hq p (congrArg Sum.inr (Sum.inr.inj (Finset.mem_singleton.1 hp)).symm)

end Blocks

/-! ## The formats at the joints of the moves -/

section Fmts
variable {E Kc : Type} [Field E] [Fintype E] {E0 : ExtSpec} {Rc Pw : Type}

/-- the format at the joint `D.mid`, where "bridge, arrangement, fold" (a link from `D.src.J` to
`D.mid`) ends: the index beside the folded word -/
def LdFoldD.fmtMid (D : LdFoldD E Kc) (i : IxAt E0 D.E₀) (rc : D.St₀ → Rc)
    (px : D.Wp → Pw) (q : Finset D.mid.E.Pos → Prop) : JFmt Kc E0 Rc Pw D.mid :=
  ⟨(i.inl D.S₁.ext).inr D.Cf.ext, fun x => rc x.2.1, fun w => px w.2.2, q⟩

theorem LdFoldD.pE_moves (D : LdFoldD E Kc) (i : IxAt E0 D.E₀) :
    D.pE.Moves ((i.inl D.S₁.ext).inr D.Cf.ext) ((i.inr D.Cf.ext).inl D.S₂.ext) :=
  ExtMap.Moves.pair_left (ExtMap.Moves.pair_right (ExtMap.Avoids.fst (i.inl D.S₁.ext) D.Cf.ext)
      (ExtMap.Moves.comp (ExtMap.Moves.fst i D.S₁.ext)
        (ExtMap.Moves.snd (i.inl D.S₁.ext) D.Cf.ext)))
    (ExtMap.Avoids.comp
      (ExtMap.Avoids.comp_moves (ExtMap.Avoids.snd i D.S₁.ext)
        (ExtMap.Moves.snd (i.inl D.S₁.ext) D.Cf.ext)) _)

theorem LdLocD.inE_moves (D : LdLocD E Kc) (i : IxAt E0 D.E₀) :
    D.inE.Moves ((i.inr D.C.ext).inl D.S.ext) ((i.inl D.S.ext).inr D.C.ext) :=
  ExtMap.Moves.pair_right (ExtMap.Avoids.comp_moves
      (ExtMap.Avoids.fst i D.C.ext) (ExtMap.Moves.fst (i.inr D.C.ext) D.S.ext))
    (ExtMap.Moves.pair_left
      (ExtMap.Moves.comp (ExtMap.Moves.snd i D.C.ext) (ExtMap.Moves.fst (i.inr D.C.ext) D.S.ext))
      (ExtMap.Avoids.snd (i.inr D.C.ext) D.S.ext))

theorem LdLocD.link_idx (D : LdLocD E Kc) (i : IxAt E0 D.E₀) :
    D.link.R.IdxLink ((i.inr D.C.ext).inl D.S.ext) (i.inl D.S.ext) :=
  IdxLink.post (IdxLink.pre (D.inE_moves i) (ldLocOf_idx D.V (D.E₀.prod D.S.ext) (i.inl D.S.ext)) _)
    (ExtMap.Moves.snd (i.inl D.S.ext) extNone) _

/-- a position after the locations, at its old place -/
def LdLocD.oldPos (D : LdLocD E Kc) : D.tgt.Ex.Pos → D.src.Ex.Pos
  | .inl p => .inl (.inr p)
  | .inr s => .inr s

end Fmts

namespace Spec

/-- One sending. -/
def ldFmt_send : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (a : LdStage E Kc)
      (d : LdSendD a) (i : IxAt E0 a.E₀) (rc : a.St → Rc) (px : a.Wp → Pw)
      (px' : d.Wp' → Pw) (q : Finset a.Ex.Pos → Prop),
    d.Hyp → (∀ w, px' (d.D.rest w).2 = px w.2) →
    d.link.Fmt (a.fmt i rc px q) (d.tgt.fmt i rc px' (a.S.qSum d.N q d.t))

/-- Many rows into one. -/
def ldFmt_bat : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (D : LdBatD E Kc)
      (i : IxAt E0 D.E₀) (rc : D.St₀ → Rc) (px : D.Wp → Pw) (q : Finset D.src.Ex.Pos → Prop),
    D.link.Fmt (D.src.fmt i (fun st => rc st.2) px q) (D.tgt.fmt i (fun st => rc st.2) px q)

/-- A row on two groups into a row on each. -/
def ldFmt_split : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (D : LdSplD E Kc)
      (i : IxAt E0 D.E₀) (rc : D.St₀ → Rc) (px : D.Wp → Pw) (q : Finset D.src.Ex.Pos → Prop),
    D.link.Fmt (D.src.fmt i (fun st => rc st.2) px q) (D.tgt.fmt i (fun st => rc st.2) px q)

/-- Bridge, arrangement, fold. -/
def ldFmt_fold : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type)
      (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid) (i : IxAt E0 D.E₀)
      (rc : D.St₀ → Rc) (px : D.Wp → Pw) (q : Finset D.src.Ex.Pos → Prop)
      (qm : Finset D.mid.E.Pos → Prop) (q' : Finset D.tgt.Ex.Pos → Prop),
    l.Fmt (D.src.fmt i (fun st => rc st.2) px q) (D.fmtMid i rc px qm) →
    (∀ U V, (∀ x, x ∈ V ↔ ∃ u ∈ U, x ∈ D.pE.src u) → q' U → qm V) →
    (D.link l).Fmt (D.src.fmt i (fun st => rc st.2) px q)
      (D.tgt.fmt (i.inr D.Cf.ext) (fun st => rc st.2) (fun w => px w.2) q')

/-- The locations. -/
def ldFmt_loc : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (D : LdLocD E Kc)
      (i : IxAt E0 D.E₀) (rc : D.St₀ → Rc) (px : D.Wp → Pw)
      (q : Finset D.src.Ex.Pos → Prop) (q' : Finset D.tgt.Ex.Pos → Prop),
    (∀ ρ U, q' U → q (D.link.R.need ρ U)) →
    D.link.Fmt (D.src.fmt (i.inr D.C.ext) (fun st => rc st.2) px q)
      (D.tgt.fmt i (fun st => rc st.2) px q')

/-- What the locations need: the t locations of the open word, and, at their old places, the
positions that what follows needs. -/
def ldFmt_loc_need : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (D : LdLocD E Kc) (ρ : Rho D.link.R.shape)
      (U : Finset D.tgt.Ex.Pos) (q : D.src.Ex.Pos),
    q ∈ D.link.R.need ρ U ↔ (∃ k : Fin D.t, q = Sum.inl (Sum.inl (ρ.1 k))) ∨ ∃ u ∈ U, q = D.oldPos u

/-- A reduction on claims about the messages, lifted over the oracle messages of a stage. -/
def ldFmt_lift : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc : Type) (a : LdStage E Kc)
      (St' Wp' : Type) (E₀' : ExtSpec) (B : Rels Kc St' E₀' (a.S.Msg × Wp'))
      (R : IOR a.St a.E₀ St' E₀') (H : R.Honest (a.S.Msg × a.Wp) (a.S.Msg × Wp'))
      (ext : a.S.Msg → a.St × a.E₀.Str → Tr R.shape → Wp' → a.Wp) (P : Nums Kc R) (i : IxAt E0 a.E₀)
      (i' : IxAt E0 E₀') (rc : a.St → Rc) (rc' : St' → Rc),
    (R.IdxLink i i' → (a.lift B R H ext P).R.IdxLink (i.inl a.S.ext) (i'.inl a.S.ext)) ∧
    (R.Passes rc rc' → (a.lift B R H ext P).R.Passes (fun x => rc x.1) (fun x => rc' x.1))

/-- A step without rounds. -/
def ldFmt_step : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type) (a b : LdStage E Kc)
      (f : a.X → Option b.X) (g : ExtMap a.Ex b.Ex) (m : a.X × a.W → b.X × b.W)
      (back : a.X × a.Ex.Str → b.W → a.W) (φ : JFmt Kc E0 Rc Pw a.J) (ψ : JFmt Kc E0 Rc Pw b.J),
    g.Moves φ.ix ψ.ix → (∀ x x', f x = some x' → ψ.rc x' = φ.rc x) →
    (∀ p, ψ.px (m p).2 = φ.px p.2) → (∀ U V, (∀ x, x ∈ V ↔ ∃ u ∈ U, x ∈ g.src u) → ψ.q U → φ.q V) →
    (LdMv.step a b f g m back).Fmt φ ψ

/-- The named moves, as statements on moves. -/
def ldFmt_mv : Prop :=
  ∀ (E Kc : Type) [Field E] [Fintype E] (E0 : ExtSpec) (Rc Pw : Type),
    (∀ (a : LdStage E Kc) (d : LdSendD a) (φ : JFmt Kc E0 Rc Pw a.J) (ψ : JFmt Kc E0 Rc Pw d.tgt.J),
      d.link.Fmt φ ψ → (LdMv.send a d).Fmt φ ψ) ∧
    (∀ (a b : LdStage E Kc) (c : Chain Kc a.J b.J)
          (φ : JFmt Kc E0 Rc Pw a.J) (ψ : JFmt Kc E0 Rc Pw b.J),
        c.Fmt φ ψ → (LdMv.sub a b c).Fmt φ ψ) ∧
    (∀ (D : LdBatD E Kc) (φ : JFmt Kc E0 Rc Pw D.src.J) (ψ : JFmt Kc E0 Rc Pw D.tgt.J),
      D.link.Fmt φ ψ → (LdMv.bat D).Fmt φ ψ) ∧
    (∀ (D : LdSplD E Kc) (φ : JFmt Kc E0 Rc Pw D.src.J) (ψ : JFmt Kc E0 Rc Pw D.tgt.J),
      D.link.Fmt φ ψ → (LdMv.split D).Fmt φ ψ) ∧
    (∀ (D : LdFoldD E Kc) (l : Link Kc D.src.J D.mid)
          (φ : JFmt Kc E0 Rc Pw D.src.J) (ψ : JFmt Kc E0 Rc Pw D.tgt.J),
        (D.link l).Fmt φ ψ → (LdMv.fold D l).Fmt φ ψ) ∧
    (∀ (D : LdLocD E Kc) (φ : JFmt Kc E0 Rc Pw D.src.J) (ψ : JFmt Kc E0 Rc Pw D.tgt.J),
      D.link.Fmt φ ψ → (LdMv.loc D).Fmt φ ψ)

end Spec

theorem ldFmt_send : Spec.ldFmt_send := by
  intro E Kc _ _ E0 Rc Pw a d i rc px px' q h hp
  refine ⟨IdxLink.post (ldSendFam_idx d.N d.Sd _ _ (i.inl a.S.ext)) (mergeE_moves a.S d.N a.E₀ i) _,
    ?_, ?_, ?_⟩
  · refine Passes.post (r₂ := fun x : (a.St × a.S.Smp) × d.N.Smp => rc x.1.1) ?_ _ _ ?_
    · intro x y τ x' hx
      cases hx
      rfl
    · intro x x' hx
      cases hx
      rfl
  · refine Honest.Hands.post
      (p₂ := fun v : d.N.Wit × (a.S.Wit × d.Wp') => px' v.2.2) ?_ _ _ _ fun _ => rfl
    intro x y w c ρ _ _
    exact hp w
  · exact (ldSendSig_piece E a.S d.N d.Sd Kc a.St a.Wp d.Wp' a.E₀ a.A d.bk d.D d.L d.t q h.laws
      h.fair h.list h.evades h.sender h.blind h.hides).bears

theorem ldFmt_bat : Spec.ldFmt_bat := by
  intro E Kc _ _ E0 Rc Pw D i rc px q
  have hc := OnlyCopies.draw D.Z.D (ldBatSigNx D.S D.Sb D.Z D.St₀) (D.E₀.prod D.S.ext)
  refine ⟨IdxLink.of_copies hc _, Passes.draw _ _ _ _ _ fun _ _ => rfl,
    ?_, hc.bears _ (fun _ => trivial) q⟩
  exact Honest.Hands.draw D.Z.D (ldBatSigNx D.S D.Sb D.Z D.St₀) (D.E₀.prod D.S.ext)
    (D.S.Wit × D.Wp) _ fun w => px w.2

theorem ldFmt_split : Spec.ldFmt_split := by
  intro E Kc _ _ E0 Rc Pw D i rc px q
  have hc := ldSay_copies (0 : E) (splitNx D.S D.St₁ D.St₂ D.St₀) (D.E₀.prod D.S.ext)
  refine ⟨IdxLink.of_copies hc _, ?_, fun _ _ _ _ _ _ _ => rfl, hc.bears _ (fun _ => trivial) q⟩
  intro x y τ x' hx
  cases hx
  rfl

theorem ldFmt_fold : Spec.ldFmt_fold := by
  intro E Kc _ _ E0 Rc Pw D l i rc px q qm q' h hq
  exact ⟨IdxLink.post h.idx (D.pE_moves i) _,
    Passes.post h.pass _ _ (fun x x' hx => by cases hx; rfl),
    Honest.Hands.post h.hands _ _ _ (fun _ => rfl),
    bears_post _ _ _ _ _ _ _ h.bears hq⟩

theorem ldFmt_loc : Spec.ldFmt_loc := by
  intro E Kc _ _ E0 Rc Pw D i rc px q q' hq
  refine ⟨D.link_idx i, ?_, fun _ _ _ _ _ _ _ => rfl, fun ρ U hU => ⟨trivial, hq ρ U hU⟩⟩
  intro x y τ x' hx
  cases hx
  rfl

theorem ldFmt_loc_need : Spec.ldFmt_loc_need := by
  intro E Kc _ _ D ρ U q
  have hA : ∀ (x : D.P) (z : D.src.Ex.Pos),
      z ∈ D.inE.src (Sum.inl x) ↔ z = Sum.inl (Sum.inl x) := fun x z => by
    constructor
    · intro h
      obtain ⟨a, ha, hz⟩ := ldSendP_mem_biUnion.1 h
      obtain rfl := Finset.mem_singleton.1 ha
      exact Finset.mem_singleton.1 hz
    · rintro rfl
      exact ldSendP_mem_biUnion.2
        ⟨Sum.inl x, Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩
  have hB : ∀ (u : D.tgt.Ex.Pos) (z : D.src.Ex.Pos),
      z ∈ D.inE.src (Sum.inr u) ↔ z = D.oldPos u := fun u z => by
    cases u with
    | inl p =>
        constructor
        · intro h
          obtain ⟨a, ha, hz⟩ := ldSendP_mem_biUnion.1 h
          obtain rfl := Finset.mem_singleton.1 ha
          exact Finset.mem_singleton.1 hz
        · rintro rfl
          exact ldSendP_mem_biUnion.2
            ⟨Sum.inr p, Finset.mem_singleton_self _, Finset.mem_singleton_self _⟩
    | inr s => exact Finset.mem_singleton
  have hS : ∀ (u : D.tgt.Ex.Pos) (z : D.src.Ex.Pos),
      z ∈ D.link.R.srcE ρ u ↔ z = D.oldPos u := fun u z => by
    constructor
    · intro h
      obtain ⟨a, ha, hz⟩ := ldSendP_mem_biUnion.1 h
      obtain rfl := Finset.mem_singleton.1 ha
      obtain ⟨b, hb, hz⟩ := ldSendP_mem_biUnion.1 hz
      obtain rfl := Finset.mem_singleton.1 hb
      exact (hB u z).1 hz
    · intro h
      exact ldSendP_mem_biUnion.2
        ⟨Sum.inr u,
          Finset.mem_singleton_self _,
          ldSendP_mem_biUnion.2 ⟨Sum.inr u, Finset.mem_singleton_self _, (hB u z).2 h⟩⟩
  rw [mem_need, IOR.mem_given]
  constructor
  · rintro ((h | ⟨p, _, h⟩) | ⟨u, hu, h⟩)
    · obtain ⟨z, hz, hq⟩ := ldSendP_mem_biUnion.1 h
      obtain ⟨k, _, rfl⟩ := ldSendP_mem_image.1 hz
      exact Or.inl ⟨k, (hA _ q).1 hq⟩
    · obtain ⟨z, hz, _⟩ := ldSendP_mem_biUnion.1 h
      exact absurd hz (Finset.notMem_empty _)
    · exact Or.inr ⟨u, hu, (hS u q).1 h⟩
  · rintro (⟨k, rfl⟩ | ⟨u, hu, rfl⟩)
    · exact Or.inl
        (Or.inl (ldSendP_mem_biUnion.2
            ⟨Sum.inl (ρ.1 k), ldSendP_mem_image.2 ⟨k, Finset.mem_univ k, rfl⟩, (hA _ _).2 rfl⟩))
    · exact Or.inr ⟨u, hu, (hS u _).2 rfl⟩

theorem ldFmt_lift : Spec.ldFmt_lift := fun _ _ _ _ _ _ a _ _ _ _ _ _ _ _ _ _ _ _ =>
  ⟨fun h => IdxLink.keepE_left (IdxLink.keepX h a.S.Smp) a.S.ext,
    fun h => Passes.keepE (Passes.keepX h a.S.Smp) a.S.ext⟩

theorem ldFmt_step : Spec.ldFmt_step := by
  classical
  intro E Kc _ _ E0 Rc Pw a b f g m back φ ψ hg hf hm hq
  refine (Chain.fmt_one _ φ ψ).2
    ⟨IdxLink.pure hg f, fun x _ _ x' hx => hf x x' hx,
      fun x _ w _ _ _ _ => hm (x, w), fun ρ U hU => ⟨trivial, ?_⟩⟩
  refine hq U _ (fun x => ?_) hU
  rw [mem_need, IOR.mem_given]
  constructor
  · rintro ((h | ⟨p, _, _⟩) | h)
    · exact absurd h (Finset.notMem_empty _)
    · exact p.elim
    · exact h
  · exact Or.inr

theorem ldFmt_mv : Spec.ldFmt_mv := fun _ _ _ _ _ _ _ =>
  ⟨fun _ _ φ ψ h => (Chain.fmt_one _ φ ψ).2 h,
    fun _ _ _ _ _ h => h,
    fun _ φ ψ h => (Chain.fmt_one _ φ ψ).2 h,
    fun _ φ ψ h => (Chain.fmt_one _ φ ψ).2 h,
    fun _ _ φ ψ h => (Chain.fmt_one _ φ ψ).2 h,
    fun _ φ ψ h => (Chain.fmt_one _ φ ψ).2 h⟩

end Cb
