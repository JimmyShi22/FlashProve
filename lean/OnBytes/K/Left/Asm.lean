-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/K/Left/Asm.lean: what the strict reader of a chain has read can be typed: from the reader's
equation `Fmt.readChainX h S seen b i = some (o, j)` to the three premises of `assembleS_isSome`
(OnBytes/TypedOracleCompiler/Slice/EntryTyping.lean), and so to `assembleS D dec o = some π`.

Main names (h: any hash whose answers have the format's lengths; S: any description):
  `run_of_read`: a chain that has random bytes has a run value, of 32 bytes.
  `kinds_of_trace`, `kinds_of_read`: each round's values as read are of the kinds of its items.
  `plains_of_read`: so the rounds' plain parts can be typed (`PQ.plainsSL`).
  `shapes_of_trace`: each opening as read has the shape that the description gives its tree.
  `given32_of_read`: the digests that the reader of an opening has read have 32 bytes.
  `paths_of_chain`: every listed place of every opening of every round has its whole path among the
    vertices met.
  `asm_of_read`: the typed string is there.
  `asm_eq`: the same at the entry's description `entryXD G c` (OnBytes/TypedOracleCompiler/Slice/EntryDesc.lean), at
    the format's own oracle, whatever the statement: no hypothesis but the reader's equation.

Hypotheses: the reader's equation; the lengths of h's answers; `S.base.rand ≠ .none`; D's rounds are
those of S's description.

Limits: values alone: that a string can be typed says nothing on whether any verifier accepts it.
Nothing on soundness; no probability.

Terms: lean/GLOSSARY.md.

-/
import OnBytes.Tie.TraceStrict
import OnBytes.TypedOracleCompiler.Slice.EntryTyping
import OnBytes.TypedOracleCompiler.Slice.Batch3SRead2
import OnBytes.TypedOracleCompiler.Slice.EntryDesc
import OnBytes.TypedOracleCompiler.Run.PageXTop
import Run.OpenDomProofs
import Run.PageIsTopProofs

set_option autoImplicit false

namespace OnBytes.K.Left
open OnBytes.Tie TypedOracleCompiler.Slice
open _root_.Run (pathFrom HId)
open _root_.Run.PQ (TraceL)

/-- What holds along two lists holds of each member of the second, with some member of the first. -/
theorem forall₂_mem_right {α β : Type} {R : α → β → Prop} :
    ∀ {l : List α} {l' : List β}, List.Forall₂ R l l' → ∀ y ∈ l', ∃ x ∈ l, R x y
  | _, _, .nil, _, hy => absurd hy List.not_mem_nil
  | _, _, .cons (a := a) r rs, y, hy => by
      rcases List.mem_cons.1 hy with rfl | hy
      · exact ⟨a, List.mem_cons_self, r⟩
      · obtain ⟨x, hx, hr⟩ := forall₂_mem_right rs y hy
        exact ⟨x, List.mem_cons_of_mem _ hx, hr⟩

section
variable (h : HId)

/-- Each round's values are of the kinds of its items. -/
theorem kinds_of_trace (S₀ : Fmt.Spec) (P : Fmt.Plan) :
    ∀ (rs : List Fmt.Round) (ros : List Fmt.RoundOut) (c : Fmt.Chain) (roots : Array ByteArray)
        (sent : ℕ), TraceL h P rs ros c roots →
      List.Forall₂ (fun d r => (_root_.Run.PQ.PlainOf.ofGots d.items r.vals).isSome = true)
        (TypedOracleCompiler.Run.PQ.rdsFrom S₀ sent rs) ros
  | [], [], _, _, _, _ => .nil
  | r :: rs, ro :: ros, c, roots, sent, t => by
    obtain ⟨-, hv, -, -, -, t'⟩ := t
    obtain ⟨p, hp⟩ := _root_.Run.PQ.ofGots_whole P.field r.items ro.msg ro.vals hv
    refine .cons ?_ (kinds_of_trace S₀ P rs ros _ _ (sent + r.entry.roots) t')
    show (_root_.Run.PQ.PlainOf.ofGots r.items ro.vals).isSome = true
    rw [hp]
    rfl

/-- Each opening has the shape that the description gives its tree. -/
theorem shapes_of_trace (P : Fmt.Plan) :
    ∀ (rs : List Fmt.Round) (ros : List Fmt.RoundOut) (c : Fmt.Chain) (roots : Array ByteArray),
      TraceL h P rs ros c roots →
      List.Forall₂ (fun r ro => List.Forall₂ (fun x y => y.1 = x.1) r.opens ro.opens) rs ros
  | [], [], _, _, _ => .nil
  | r :: rs, ro :: ros, c, roots, t => by
    obtain ⟨-, -, -, -, ho, t'⟩ := t
    exact .cons (ho.imp fun _ _ f => f.sh) (shapes_of_trace P rs ros _ _ t')

/-- The digests that the reader of an opening has read have 32 bytes. -/
theorem given32_of_read (cfg : ByteArray) (f : Fmt.Fld) (sb : ℕ) (sh : Fmt.Shape)
    (start : ByteArray) (xs : List ℕ) (b : ByteArray) (i : ℕ) (o : Fmt.OpenOut)
    (e : Fmt.readOpeningW (m := Id) h cfg f sb sh start xs b i = some o) :
    ∀ g ∈ o.given, g.size = 32 := by
  obtain ⟨-, cs, hp, -, -⟩ := _root_.Run.PQ.readOpening_some h cfg f sb sh start xs b i o e
  exact (_root_.Run.rdOpening_parts f sb sh xs b i cs o.given o.next hp).2

variable {h} (hz : ∀ n t i s b, ByteArray.size (h n t i s b) = Fmt.dlen n)
  {S : Fmt.SpecX} {seen : Fmt.Seen} {b : ByteArray} {i : ℕ} {o : Fmt.ChainOut} {j : ℕ}
  (e : Fmt.readChainX (m := Id) h S seen b i = some (o, j))

include e in
/-- Each round's values as read are of the kinds of its items. S₀: the description from which the
rounds' data take the forms of the trees; the items are the rounds' own. -/
theorem kinds_of_read (S₀ : Fmt.Spec) :
    List.Forall₂ (fun d r => (_root_.Run.PQ.PlainOf.ofGots d.items r.vals).isSome = true)
      (TypedOracleCompiler.Run.PQ.rdsFrom S₀ 0 S.base.rounds) o.rounds.toList := by
  obtain ⟨-, -, rc, g1, g2, -, -⟩ := readX_trace h S seen b i o j e
  have k := kinds_of_trace h S₀ S.base.plan _ _ _ _ 0 g2
  rw [g1]
  exact List.forall₂_map_right_iff.2 (List.forall₂_map_right_iff.1 k)

include e in
/-- The rounds' plain parts can be typed. -/
theorem plains_of_read (S₀ : Fmt.Spec) (C : TypedOracleCompiler.Run.PQ.CK) :
    ∃ pls, TypedOracleCompiler.Run.PQ.plainsSL C (TypedOracleCompiler.Run.PQ.rdsFrom S₀ 0 S.base.rounds)
      o.rounds.toList = some pls :=
  Option.isSome_iff_exists.1 (plainsSL_isSome C _ _ (kinds_of_read e S₀))

include hz e in
/-- A chain that has random bytes has a run value, of 32 bytes. -/
theorem run_of_read (hr : S.base.rand ≠ .none) : ∃ run, o.run = some run ∧ run.size = 32 := by
  obtain ⟨run, hrun⟩ := readX_run h S seen b i o j e hr
  obtain ⟨x, i0, hd, -, hst, h1, -⟩ := readX_head h S seen b i o j e
  refine ⟨run, hrun, ?_⟩
  rw [hrun] at h1
  unfold Fmt.startChainW at hst
  split at hst
  · split at hst
    · simp only [_root_.Run.idb, _root_.Run.idp] at hst
      obtain rfl := Option.some.inj hst
      cases h1
    · split at hst
      · simp only [_root_.Run.idb] at hst
        split at hst
        · simp only [_root_.Run.idp] at hst
          obtain rfl := Option.some.inj hst
          obtain rfl := Option.some.inj h1
          exact hz 172 _ _ _ _
        · cases hst
      · cases hst
  · cases hst

include hz e in
/-- Every listed place of every opening of every round has its whole path among the vertices
met. -/
theorem paths_of_chain : ∀ op ∈ opsOf 1 o, ∀ z ∈ op.xs.zip (op.out.cols.zip op.out.salts),
    (pathFrom op.sh.a op.out.seen z.1).isSome = true := by
  obtain ⟨hok, -, rc, g1, g2, -, g5⟩ := readX_trace h S seen b i o j e
  have hlen : S.stored.length = S.base.rounds.length := by
    have := hok
    simp only [Fmt.SpecX.ok, Bool.and_eq_true, beq_iff_eq] at this
    exact this.1.2
  have hzp : (S.base.rounds.zip S.stored).map (·.1) = S.base.rounds :=
    List.map_fst_zip (by omega)
  have sh1 := List.forall₂_map_right_iff.1 (shapes_of_trace h S.base.plan _ _ _ _ g2)
  rw [← hzp] at sh1
  have sh2 := List.forall₂_map_left_iff.1 sh1
  have all := forall₂_and sh2 g5
  refine ops1_all (fun y => ∀ z ∈ y.2.1.zip (y.2.2.cols.zip y.2.2.salts),
    (pathFrom y.1.a y.2.2.seen z.1).isSome = true) o fun r hr y hy => ?_
  rw [g1] at hr
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hr
  obtain ⟨x, -, hs, -, hown, hsto⟩ := forall₂_mem_right all p hp
  have hs' : List.Forall₂ (fun a c => c.1 = a.1) x.1.opens p.1.opens :=
    List.forall₂_map_right_iff.1 hs
  rcases List.mem_append.1 (show y ∈ p.2 ++ p.1.opens from hy) with hy | hy
  · obtain ⟨t, -, hf, i', hrd⟩ := forall₂_mem_right hsto y hy
    have R : ReadAs h S.base.cfg S.base.cfg ⟨1, 0, 0, y.1, y.2.1, y.2.2⟩ :=
      ⟨⟨S.base.plan.field, t.salt, b, i', by rw [hf.sh]; exact hrd⟩,
        given32_of_read h _ _ _ _ _ _ _ _ _ hrd⟩
    exact paths_of_read hz R
  · obtain ⟨a, -, hsh, start, i', -, hrd, -⟩ := forall₂_mem_right (forall₂_and hs' hown) y hy
    have R : ReadAs h S.base.cfg start ⟨1, 0, 0, y.1, y.2.1, y.2.2⟩ :=
      ⟨⟨S.base.plan.field, S.base.plan.salt, b, i', by rw [hsh]; exact hrd⟩,
        given32_of_read h _ _ _ _ _ _ _ _ _ hrd⟩
    exact paths_of_read hz R

include hz e in
/-- The typed string is there. D: a description with stored tables whose rounds are those that
the reader was given. -/
theorem asm_of_read {X : Type} (D : TypedOracleCompiler.Run.PQ.XD) (dec : X → _root_.Run.PQ.View → Bool)
    (hr : S.base.rand ≠ .none) (hD : D.base.rounds = S.base.rounds) :
    ∃ π, assembleS D dec o = some π := by
  obtain ⟨run, hrun, -⟩ := run_of_read hz e hr
  refine Option.isSome_iff_exists.1 (assembleS_isSome D dec o (by rw [hrun]; rfl) ?_
    (paths_of_chain hz e))
  show List.Forall₂ _ (TypedOracleCompiler.Run.PQ.rdsFrom D.base 0 D.base.rounds) _
  rw [hD]
  exact kinds_of_read e D.base

end

/-- At the entry's description: what the strict reader, at the format's own oracle, has read
under the program's description of the entry's chain at G's parameters, with c for the digest and
any statement, can be typed at `entryXD G c`, whatever the decision. -/
theorem asm_eq (G : EntryGround) (c st : ByteArray) {seen : Fmt.Seen} {b : ByteArray} {i : ℕ}
    {o : Fmt.ChainOut} {j : ℕ}
    (e : Fmt.readChainX (m := Id) (Fmt.HO Fmt.oracle)
      (TypedOracleCompiler.Run.PQ.withStatement (Params.entrySpecOf (linkAtCfg G.q c) G.rs ByteArray.empty) st)
      seen b i = some (o, j))
    {X : Type} (dec : X → _root_.Run.PQ.View → Bool) :
    ∃ π, assembleS (entryXD G c) dec o = some π :=
  asm_of_read (_root_.Run.PQ.size_HO Fmt.oracle Fmt.size_oracle) e (entryXD G c) dec
    (fun h => by cases h) rfl

end OnBytes.K.Left
