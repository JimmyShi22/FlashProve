-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
AtFullSide/K2/SymbolsOfMembers.lean: SymbolsAre at a yes of the code switch, at what the closing
returned, from one record for each member of the closed group.

  MemberSent    one member, or the fresh mask: the plan and the rows that sent it, where the book
                seats it, and that the thread's table of its tree is the sending's
  MemberRow     the further clauses of a member of the group
  symbols_of_closing   the two records at each member, and the closing's return, give SymbolsAre

Limits. Every record is a premise: nothing here says that a run meets it. The rows of a record hold
a run's coins.
-/
import AtFullSide.K2.SymbolsAtFold
import AtFullSide.K2.FrontLay
import Johnson.Desc.ProofFile.Honest.K2.Law.SymbolsAtThread

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace AtFullSide.K2
open OnBytes
open OnBytes.Slice (GE readL codeOf)
open Johnson.Prover.Send (Rows shapeAt)
open VerifiableInference.Desc (Block OpenedColumn)
open VerifiableInference.Desc.K2.Honest (Left Sizes GroupMember SymbolsAre foldEndAt groupLayout
  keptNo keptOf shapeOf symbols_at_thread zeroG)
open VerifiableInference.Desc.First.K2 (P2 rounds AtYes)
open ProofFile.Honest (ProverCoinCounts Coins Env Mid Played Thr Thread fillCols readsOf treesTo)
open ProofFile.Honest.K1 (treeTables)
open ProofFile.Honest.K2 (GroupRows SegmentPub challengesOr0 freshTable frozenLeft segmentLeft segmentGroupRows
  zeroMessage)

/-- **One message that the closed group reads**, number w in the list of messages to open: P, Vr,
kn: the sending's plan, its rows, the message's number in it. Xo: the message in the statement
behind the switch's sending. pp, tr: its seat and its tree in that book. -/
structure MemberSent {St Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk St Cl V W X Pb) (n₀ : Nat)
    (k : Coins Bk) (m : Mid W X) (q : P2) (Z : Sizes) (old : SingleRows) (z : _root_.Tw.K2.Sent)
    (w : Nat) (P : VerifiableInference.Desc.K1.Par) (Vr : Nat → Rows) (kn : Nat) (Xo : Oracle)
    (pp : Nat × Nat) (tr : Tree) : Prop where
  plan : VerifiableInference.Desc.K1.planOkOwn P = true
  below : kn < P.sent.size
  oracle : Xo.shape = shapeAt P kn
  maskCode : (shapeAt P kn).maskRows ≠ 0 →
    P.codes.mask.getD (shapeAt P kn).maskCode default = Z.codes.mask.getD Z.maskCode default
  place : ∀ hw : w < (singleRowsOracles old).size,
    z.book.place[(singleRowsOracles old)[w]]? = some pp
  stated : ∀ hw : w < (singleRowsOracles old).size,
    z.st.oracles[(singleRowsOracles old)[w]]? = some Xo
  tree : z.book.trees[pp.1]? = some tr
  treeShape : tr.shape = ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).shapes.getD
    (((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree.getD kn 0) {}
  part : pp.2 = ((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).part.getD kn 0
  logMask : (shapeAt P kn).maskRows ≠ 0 →
    (codeOf (Z.codes.mask.getD Z.maskCode default)).a ≤ tr.shape.logN
  front : tr.number - q.firstTree < treesTo T.bs n₀
  table : (treeTables P Vr)[((VerifiableInference.Desc.Own.treesMade P.codes P.sent).getD {}).tree.getD
    kn 0]? = some (T.tableAt (.own (tr.number - q.firstTree)) k m).2

/-- **The further clauses of a member of the group**: its shape, its main code and its tree's length,
and that the sender's rows are those that the closing laid anew. -/
structure MemberRow (q : P2) (Z : Sizes) (ms : List GroupMember) (R : GroupRows) (w : Nat)
    (P : VerifiableInference.Desc.K1.Par) (Vr : Nat → Rows) (kn : Nat) (tr : Tree) : Prop where
  shape : shapeOf ms w = shapeAt P kn
  mainCode : (shapeAt P kn).mainRows ≠ 0 →
    P.codes.base.getD (shapeAt P kn).code default = Z.codes.base.getD Z.code default
  logMain : (shapeOf ms w).mainRows ≠ 0 → tr.shape.logN = q.logN
  rows : R.rows.getD w zeroMessage = Vr kn

/-- **The further clauses of the fresh mask**: enough mask rows, and that it folds as the mask that
the closing laid anew. -/
structure FreshRow (old : SingleRows) (R : GroupRows) (P : VerifiableInference.Desc.K1.Par)
    (Vr : Nat → Rows) (kn : Nat) : Prop where
  maskRows : 2 ^ old.layout.h ≤ (shapeAt P kn).maskRows
  mask : (R.fresh.getD zeroMessage).mask = (Vr kn).mask
  maskTl : (R.fresh.getD zeroMessage).maskTl = (Vr kn).maskTl

/-- **SymbolsAre at a yes, at what the closing returned.** -/
theorem symbols_of_closing {St Cl V W X Pb : Type} {Bk : ProverCoinCounts} (T : Thread Bk St Cl V W X Pb)
    {n₀ : Nat} {k : Coins Bk} {s : St} {m : Mid W X} {En : Env} (hA : Thr T n₀ k s m En)
    (b : Block St Cl) (q : P2) (hr : b.rounds = rounds q) (hft : T.ft = q.firstTree)
    (rs : List Fmt.RoundView) (cols : List OpenedColumn) (hF : b.Fits q.firstTree rs cols) (ps : List Played)
    (R1 R2 : Fmt.Drawn)
    (hfill : fillCols (readsOf T.chain T.ft (En.add ps).stored (En.add ps).tree b.rounds [R1, R2])
      [] = .ok cols)
    {s₁ t : VerifiableInference.Desc.First.S} {r₁ r₂ : Fmt.RoundView} {x : _root_.Tw.K2.Front}
    {z : _root_.Tw.K2.Sent} {S3 : Statement} {Y : Array E} {rows : List OnBytes.Row} {G : Group}
    {cd : Code} (A : AtYes q s₁ t r₁ r₂ (b.shown q.firstTree rs cols) x z S3 Y rows G cd)
    (Z : Sizes) (ms : List GroupMember) (γ : List GE) (L : FrontLay Z ms γ x.f.rows)
    (hpos : ∀ j, j < (Positions.ofDraws q.logN r₂.drawn.poss).all.size →
      (Positions.ofDraws q.logN r₂.drawn.poss).all.getD j 0 < 2 ^ q.logN)
    {Sg : SegmentPub} {prev : Option Left} {prevKept : List OracleShape}
    {own : Nat → Nat → Nat → Cb.Gl.E} {heard : List Fmt.Drawn}
    {kk : Nat → Except String ProofFile.Honest.K2.Stretch} {base : Nat} {Wl : Left} {R : GroupRows}
    (hL : segmentLeft freshTable Sg prev prevKept own heard kk base = .ok (Wl, Z.kept))
    (hR : segmentGroupRows freshTable Sg prev prevKept own kk base true = .ok R)
    (hc : Sg.sizes.codes = Z.codes) (hcode : Sg.sizes.code = Z.code)
    (hmask : Sg.sizes.maskCode = Z.maskCode) (hms : R.members = ms)
    (hγ : challengesOr0 heard Sg.gamma = γ)
    (l1 : (groupLayout Z.codes Z.code Z.maskCode ms).k = x.f.rows.layout.k)
    (l2 : (groupLayout Z.codes Z.code Z.maskCode ms).h = x.f.rows.layout.h)
    (l3 : (groupLayout Z.codes Z.code Z.maskCode ms).mainFirst = x.f.rows.layout.mainFirst)
    (l4 : (groupLayout Z.codes Z.code Z.maskCode ms).maskFirst = x.f.rows.layout.maskFirst)
    (hK : ∀ a, a < Z.kept.length → keptNo ms a < ms.length)
    (hall : ∀ w, w ≤ x.f.rows.layout.members.size →
      ∃ (P : VerifiableInference.Desc.K1.Par) (Vr : Nat → Rows) (kn : Nat) (Xo : Oracle)
        (pp : Nat × Nat) (tr : Tree),
        MemberSent T n₀ k m q Z x.f.rows z w P Vr kn Xo pp tr ∧
        (w < x.f.rows.layout.members.size → MemberRow q Z ms R w P Vr kn tr) ∧
        (w = x.f.rows.layout.members.size → FreshRow x.f.rows R P Vr kn)) :
    SymbolsAre Z x.f.rows Wl (Positions.ofDraws q.logN r₂.drawn.poss) Y := by
  obtain ⟨P₀, V₀, k₀, X₀, p₀, t₀, -⟩ := hall 0 (Nat.zero_le _)
  have H : ∀ w, ∃ (P : VerifiableInference.Desc.K1.Par) (Vr : Nat → Rows) (kn : Nat) (Xo : Oracle)
      (pp : Nat × Nat) (tr : Tree), w ≤ x.f.rows.layout.members.size →
        MemberSent T n₀ k m q Z x.f.rows z w P Vr kn Xo pp tr ∧
        (w < x.f.rows.layout.members.size → MemberRow q Z ms R w P Vr kn tr) ∧
        (w = x.f.rows.layout.members.size → FreshRow x.f.rows R P Vr kn) := by
    intro w
    by_cases hw : w ≤ x.f.rows.layout.members.size
    · obtain ⟨P, Vr, kn, Xo, pp, tr, e⟩ := hall w hw
      exact ⟨P, Vr, kn, Xo, pp, tr, fun _ => e⟩
    · exact ⟨P₀, V₀, k₀, X₀, p₀, t₀, fun h => absurd h hw⟩
  choose Pw Vw kw Xw pw tw H using H
  have hlen : ∀ w, w < (singleRowsOracles x.f.rows).size → w ≤ x.f.rows.layout.members.size := by
    intro w hw
    unfold singleRowsOracles at hw
    rw [L.masks] at hw
    simp only [beq_self_eq_true, if_true, Array.size_push] at hw
    omega
  refine symbols_of_fold (fun w => Vw w (kw w))
    (Vw x.f.rows.layout.members.size (kw x.f.rows.layout.members.size)) γ hL hR hc hcode hmask hms
    hγ l1 l2 l3 l4
    (fun w hw => ((H w (by rw [L.length] at hw; omega)).2.1 (by rw [L.length] at hw; exact hw)).rows)
    ((H _ (Nat.le_refl _)).2.2 rfl).mask ((H _ (Nat.le_refl _)).2.2 rfl).maskTl hK
    (symbols_at_thread T hA b q hr hft rs cols hF ps R1 R2 hfill A Z ms γ Pw Vw kw Xw pw tw L.masks
      L.keptRows L.gamma L.keptShapes L.keptNos L.keptFirst L.apartMain L.apartMask
      (fun w hw => (H w hw).1.plan) (fun w hw => (H w hw).1.below) (fun w hw => (H w hw).1.oracle)
      (fun w hw => ((H w (Nat.le_of_lt hw)).2.1 hw).shape)
      ((H _ (Nat.le_refl _)).2.2 rfl).maskRows
      (fun w hw => ((H w (Nat.le_of_lt hw)).2.1 hw).mainCode)
      (fun w hw => (H w hw).1.maskCode)
      (fun w hw => (H w (hlen w hw)).1.place hw) (fun w hw => (H w (hlen w hw)).1.stated hw)
      (fun w hw => (H w hw).1.tree) (fun w hw => (H w hw).1.treeShape)
      (fun w hw => (H w hw).1.part)
      (fun w hw => ((H w (Nat.le_of_lt hw)).2.1 hw).logMain)
      (fun w hw => (H w hw).1.logMask) hpos (fun w hw => (H w hw).1.front)
      (fun w hw => (H w hw).1.table))

end AtFullSide.K2

#print axioms AtFullSide.K2.MemberSent
#print axioms AtFullSide.K2.MemberRow
#print axioms AtFullSide.K2.FreshRow
#print axioms AtFullSide.K2.symbols_of_closing
