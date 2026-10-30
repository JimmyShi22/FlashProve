-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Maker/Page/RunsTools.lean: tools for OnBytes/Maker/Page/Runs.lean, and the record of what
that file asks of typed oracle functions.

Main definition.
  `GRows`: the nine fields of `ReadL` (OnBytes/TypedOracleCompiler/Joined/K/RunsLineRead.lean) that speak of the
    oracle functions g or of the instance in a query: the three chains' row laws, the law of the
    call in which the first chain is sealed, the three first queries, and two conditions on the
    round in which an instance is written. The fields are that record's text; one name is written
    in full; the letters that the nine do not name are left out.
Main theorems.
  `fitL_congr`: data that fit a list of rounds fit every list with the same entries, kinds and
    items.
  `room_of_fitL`: room for each round's blocks, in the format's count, from the count of the rounds'
    block samplers (`bs_blocks`, Run/PageIsProofs.lean).
  `ne₁_of_ok`: the first chain has a round before its seal, out of the tests `okAt`
    (OnBytes/Maker/Files.lean).
  `kit_at`: the kit of verifier messages as hash blocks fits a description's field (`kit_pull`).
  `rootsT_take`: the roots of a chain as read whose description's last round has no item are those
    of the rounds before the last.
  `pls₁_A`, `pls₂_A`, `pls₃_A`: the plain parts of three chains' strings in a row, chain by chain.

What is not claimed. That any g meets `GRows`. Nothing on soundness.


-/
import OnBytes.Maker.DrawsOfLine
import OnBytes.Maker.FitLine
import OnBytes.Maker.TypingLine
import OnBytes.Maker.RoundsAtTags
import OnBytes.Maker.Page.AtOracle
import Run.PageIsProofs

set_option autoImplicit false

namespace OnBytes.Maker.Page

open Rom TypedOracleCompiler.Iop TypedOracleCompiler.Joined TypedOracleCompiler.Joined.K TypedOracleCompiler.Compile.Batch
open _root_.Compile hiding ON
open _root_.Iop hiding BatchProtocol GrW WireRB RoundsQueryLayout ProtocolQueryLayout QueryLayout
open _root_.Run _root_.Run.PQ _root_.Compile.Joined
open OnBytes.Params (Rounds)

/-- Data that fit a list of rounds fit every list with the same entries, kinds and items. -/
theorem fitL_congr : ∀ (ds : List TypedOracleCompiler.Run.PQ.RD) (rs rs' : List Fmt.Round),
    TypedOracleCompiler.Run.PQ.FitL ds rs → rs.map (·.entry) = rs'.map (·.entry) →
    rs.map (·.kind) = rs'.map (·.kind) → rs.map (·.items) = rs'.map (·.items) →
    TypedOracleCompiler.Run.PQ.FitL ds rs'
  | [], [], [], _, _, _, _ => trivial
  | [], [], _ :: _, _, h, _, _ => by cases h
  | [], _ :: _, _, h, _, _, _ => h.elim
  | _ :: _, [], _, h, _, _, _ => h.elim
  | _ :: _, _ :: _, [], _, h, _, _ => by cases h
  | d :: ds, r :: rs, r' :: rs', h, he, hk, hi => by
    rw [List.map_cons, List.map_cons] at he hk hi
    obtain ⟨e1, e2⟩ := List.cons.inj he
    obtain ⟨k1, k2⟩ := List.cons.inj hk
    obtain ⟨i1, i2⟩ := List.cons.inj hi
    obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := h
    exact ⟨a1.trans e1, a2.trans k1, a3.trans i1, e1 ▸ a4, by rw [← i1, ← e1]; exact a5, e1 ▸ a6,
      fitL_congr ds rs rs' a7 e2 k2 i2⟩

/-- **Room for each round's blocks**, in the format's count, from the count of the rounds' block
samplers at data that fit the rounds. -/
theorem room_of_fitL (f : Fmt.Fld) (K : ℕ) : ∀ (ds : List TypedOracleCompiler.Run.PQ.RD) (rs : List Fmt.Round),
    TypedOracleCompiler.Run.PQ.FitL ds rs → (∀ d ∈ ds, (bsRound f d.entry d.kind).b ≤ K) →
    ∀ q ∈ rs, Fmt.blocksFor (Fmt.wordsAtMost q.entry q.kind) ≤ K
  | [], [], _, _, _, hq => by cases hq
  | [], _ :: _, h, _, _, _ => h.elim
  | _ :: _, [], h, _, _, _ => h.elim
  | d :: ds, r :: rs, h, hb, q, hq => by
    obtain ⟨a1, a2, -, -, -, -, a7⟩ := h
    rcases List.mem_cons.1 hq with rfl | hq'
    · rw [← a1, ← a2, ← bs_blocks f]
      exact hb d List.mem_cons_self
    · exact room_of_fitL f K ds rs a7 (fun d' hd' => hb d' (List.mem_cons_of_mem _ hd')) q hq'

/-- The first chain has a round before its seal, where the tests under which the data are laid pass.
-/
theorem ne₁_of_ok {a : ℕ} {R₁ R₂ R₃ : Rounds} (hok : okAt a (some (R₁, R₂, R₃)) = true) :
    (R₁.map (·.1)).dropLast ≠ [] :=
  ((someFit_iff (R₁, R₂, R₃)).1 (okAt_parts hok).rounds).1

/-- The kit of verifier messages as hash blocks fits a description's field. -/
theorem kit_at (f : Fmt.Fld) (K : ℕ) (S : Fmt.SpecX) (h : S.base.plan.field = f) :
    TypedOracleCompiler.Run.PQ.KitFits S.base.plan.field (ckP f) K (chalP f K) :=
  h ▸ kit_pull S.base.plan.field K

/-- The roots of a chain as read whose description's last round has no item are those of the rounds
before the last. -/
theorem rootsT_take (h : HId) (S : Fmt.SpecX) (seen : Fmt.Seen) (b : ByteArray) (i : ℕ)
    (o : Fmt.ChainOut) (j : ℕ) (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j))
    (rs : List Fmt.Round) (rS : Fmt.Round) (hr : S.base.rounds = rs ++ [rS]) (hi : rS.items = []) :
    rootsT o.rounds.toList = TypedOracleCompiler.Run.PQ.rootsD (o.rounds.toList.take rs.length) := by
  obtain ⟨hok, H⟩ := readX_read h S seen b i o j e
  have hm : (S.base.rounds.zip S.stored).map (·.1) = S.base.rounds :=
    List.map_fst_zip (le_of_eq (stored_length hok).symm)
  have V : List.Forall₂ (fun (r : Fmt.Round) (ro : Fmt.RoundOut) =>
      Fmt.whole (Fmt.readItems S.base.plan.field r.items) ro.msg = some ro.vals)
      S.base.rounds o.rounds.toList := by
    rw [← hm, List.forall₂_map_left_iff]
    exact H.imp fun _ _ f => f.vals
  rw [hr] at V
  have D := List.forall₂_drop_append _ rs [rS] V.flip
  obtain ⟨last, l', hl, hl', ed⟩ := List.forall₂_cons_right_iff.1 D
  obtain rfl := List.forall₂_nil_right_iff.1 hl'
  have hv : last.vals = [] := vals_nil S.base.plan.field last.msg last.vals (hi ▸ hl)
  conv_lhs => rw [← List.take_append_drop rs.length o.rounds.toList, ed]
  unfold rootsT TypedOracleCompiler.Run.PQ.rootsD
  rw [List.flatMap_append, List.flatMap_singleton, hv]
  simp [Fmt.rootsOf]

/-! ## The plain parts of three chains' strings in a row, chain by chain -/

section Parts
variable {lam : ℕ} {G : Chains} {Y : Type} {E : ExtSpec} (D : Desc G Y E) (π : OneProtocolProof lam D.batch)
  (k₁ : ChainStr lam G.c₁) (k₂ : ChainStr lam G.c₂) (k₃ : ChainStr lam G.c₃)
  (h : π.plains = plainsA G k₁ k₂ k₃)
include h

theorem pls₁_A : pls₁ D π = k₁.plains := by
  unfold pls₁
  rw [h]
  exact Plains.fst_app _ _

theorem pls₂_A : pls₂ D π = k₂.plains := by
  unfold pls₂
  rw [h]
  unfold plainsA
  rw [Plains.snd_app]
  exact Plains.fst_app _ _

theorem pls₃_A : pls₃ D π = k₃.plains := by
  unfold pls₃
  rw [h]
  unfold plainsA
  rw [Plains.snd_app]
  exact Plains.snd_app _ _

end Parts

/-! ## What is asked of g -/

section Rows
open TypedOracleCompiler.Run.Twin TypedOracleCompiler.Run.Thin TypedOracleCompiler.Run.PQ
open _root_.Run.Twin (RS up allLo allLo_eq)
open _root_.Fmt (Chain RoundOut ChainOut)
variable {I X : Type} {L : BatchProtocolWithLeafBody I X} {Y : Type} {E : ExtSpec} {C : CK} {K : ℕ} {rF rJ r3 : RS}
  {aJ : RAnn rJ.up} {ds₁ ds₂ ds₃ : List TypedOracleCompiler.Run.PQ.RD} {t : Tag}
  {D : Desc (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃) Y E}

/-- **The nine fields of `ReadL` (OnBytes/TypedOracleCompiler/Joined/K/RunsLineRead.lean) that speak of g or of the
instance in a query**, in that record's own words and letters, without the letters that these nine
do not name. -/
structure GRows
    (embP : PlainPart (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).sh (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).ann →
      PlainPart (shapeOf L t) (TypedOracleCompiler.Compile.Batch.annOf L t))
    (xin : Y → Option X) (cms : List (Dig 256)) (x : Y) (π : OneProtocolProof 256 D.batch)
    (g : Fam (typedOracleFamily 256 (K + 1) L)) (O : ByteArray → ByteArray) (rtF rt3 : List (Dig 256))
    (S₁ S₂ S₃ : _root_.Fmt.SpecX) (o₁ o₂ o₃ : ChainOut) (rs₁ : List _root_.Fmt.Round) :
    Prop where
  /-- the laws on g -/
  row₁ : RowEnd (fun _ => L) C K g t O S₁.base.label ds₁ (fun z => embL₁ embP (Sum.inr z)) (0 + 1)
    (0 + 1)
  row₂ : RowShE (fun _ => L) C K g t O S₂.base.label ds₂ (fun z => embL₂ embP (Sum.inr z))
    (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length + 1) (0 + 1)
  row₃ : RowEnd (fun _ => L) C K g t O S₃.base.label ds₃ (fun z => embL₃ embP (Sum.inr z))
    (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length +
      (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂.length + 1) (0 + 1)
  s0 : (g (OracleName.fb t) (⟨0, .f1 cms ((xin x).map L.early) π.salt, rtF,
              embL₁ embP (Sum.inl (Sum.inr (pls₁ D π).1))⟩ : FbIn 256 L t) :
    (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o₁.rho0
  sG : GAt (fun _ => L) K g t O S₁.base.label
    (embL₂ embP (Sum.inl (Sum.inr (aJ.plain (pls₂ D π).1).2)))
    (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length) (0 + rs₁.length + 1)
  s4 : (g (OracleName.fb t) (⟨0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length,
              .f4 cms (List.ofFn π.rtreq), [], embL₂ embP (Sum.inl (Sum.inl (aJ.plain (pls₂ D π).1).1))⟩ :
            FbIn 256 L t) : (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o₂.rho0
  s3 : (g (OracleName.fb t) (⟨0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length +
              (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂.length,
              .f3 (List.ofFn (bytesToDig (sealRead o₂))) (List.ofFn (bytesToDig (sealRead o₁))), rt3,
              embL₃ embP (Sum.inl (Sum.inr (pls₃ D π).1))⟩ : FbIn 256 L t) :
    (Fin (K + 1) → Dig 256) × Dig 256).2 = bytesToDig o₃.rho0
  /-- no instance is written into a query, or the round "late" is none of the stretch's -/
  late₁ : xin x = none ∨ ∀ k, k < ds₁.length → L.late ≠ some (0 + 1 + k)
  late₃ : xin x = none ∨ ∀ k, k < ds₃.length →
    L.late ≠ some (0 + (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₁.length +
      (chainsL C rF rJ r3 aJ ds₁ ds₂ ds₃).c₂.length + 1 + k)

end Rows

end OnBytes.Maker.Page
