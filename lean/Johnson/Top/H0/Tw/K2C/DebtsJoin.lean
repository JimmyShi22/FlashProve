-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-


Johnson/Top/H0/Tw/K2C/DebtsJoin.lean: the code switch: WHAT IS OWED ON THE TABLE OF JOINTS' NUMBERS
AT A SWITCH (structures LinkDebts, HandsLink.lean, and SwitchDebts,
HandsCore.lean: six fields each), JOINED OUT OF THEIR PAYERS' THEOREMS, at numbers of the form
N₀.atBlocks sh links bs: ONE CORE IN NEUTRAL LETTERS AND AN ARM A SORT OF PLACE.
  oraclesAt_len  as many trees are told as the program's layTrees lays
  told_debts   the fields trees | msgs: from what told_succ_ps concludes at the place (the two
               counts go on by what the sub-protocol there tells), where what it tells is the plan's
               oraclesAt at the sending's notices: by oraclesAt_len and told_tenants
               (ToldTenants.lean)
  debts_core   ALL SIX FIELDS: sent by switchDebts_of (SentAtPlan.lean) · carried |
               position by rows_debts (RowsDebts.lean) · trees | msgs by told_debts · keptPos
               handed through
  debts_link · debts_head · debts_finish  the arms, with the number of messages that join the group
               as each share asks it (count_of_front · count_finish)
THE PREMISES, AND WHO PAYS EACH. CLOSED, ON THE WRITTEN LIST OF SUB-PROTOCOLS AND THE PLAN: hts:
told_succ_ps (Johnson/Desc/First/ToldSucc.lean: NOT IMPORTED HERE: DebtsState.lean calls it):
its conclusion to the letter · hor: what the sub-protocol at the place tells is oraclesAt grp codes
sent · hT: the test sentFitB (sentFitAll_at) · hpos · hlen · hm. ON THE STATE: hb: the promise's
bookAt · hF, hx: the fence and the front (fence1_link | _head | _finish, MsgsBehind.lean: not
read here) · keptPos (keptPos_atLink | _atFront | _atFinish) · hTg: the front's
target is the plan's at group m (target_of_plan, PositionAtPlan.lean, or the walk's tops) · hone:
OneStored.lean's hone_of_both · hW · hl. AT THE CLOSED CONSTANT: P5J.At.N Zp cF is (numbersOf
(pseats Zp)).atBlocks (shape Zp) links cF.blocksInOrder by N_atBlocks (P5J/LettersAt.lean).
«N.groupAt m = n.grp» lies already: grp_of_id | grp_finish_of_id with
numbersOf_groupAt (GroupAtNums.lean).
LIMITS. A join. None of the premises is shown at a real value here. At m = 0 nothing is said. No
soundness is claimed.
-/
import Johnson.Top.H0.Tw.K2C.SentAtPlan
import Johnson.Top.H0.Tw.K2C.ToldTenants
import Johnson.Top.H0.Tw.K2C.RowsDebts

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace VerifiableInference.Desc.First.K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Place Block)
open _root_.Tw.K2 (switchNotices firstFront)
open P1K2 (oraclesAt)

/-- As many trees are told as the program's layTrees lays. -/
theorem oraclesAt_len {grp : Nat} {codes : Codes} {sent : Array OracleNotice} {lay : TreeLay}
    (h : layTrees codes sent = some lay) : (oraclesAt grp codes sent).length = lay.shapes.size := by
  unfold oraclesAt
  rw [h]
  simp

section
variable {St Cl : Type} {N₀ : Numbers} {sh : Params.ReqShape} {links : List ModelPart}
  {bs : List (Block St Cl)} {ps : List Place}

/-- **The two counts at a switch's place**: the fields trees and msgs of the two structures. -/
theorem told_debts {k : Nat} {b : Block St Cl}
    (hts : (N₀.atBlocks sh links bs).treesAt ps[k + 1]? =
        (N₀.atBlocks sh links bs).treesAt ps[k]? + b.oracles.flatten.length ∧
      (N₀.atBlocks sh links bs).msgsAt ps[k + 1]? =
        (N₀.atBlocks sh links bs).msgsAt ps[k]? +
          (b.oracles.flatten.map fun o => o.tenants.length).sum)
    {grp : Nat} {codes : Codes} {sent : Array OracleNotice}
    (hor : b.oracles.flatten = oraclesAt grp codes sent) {x : _root_.Tw.K2.Front}
    (hn : switchNotices x.T x.others = sent) (hc : x.st.codes = codes) {lay : TreeLay}
    (hl : layTrees x.st.codes (switchNotices x.T x.others) = some lay) :
    (N₀.atBlocks sh links bs).treesAt ps[k + 1]? =
        (N₀.atBlocks sh links bs).treesAt ps[k]? + lay.shapes.size ∧
      (N₀.atBlocks sh links bs).msgsAt ps[k + 1]? =
        (N₀.atBlocks sh links bs).msgsAt ps[k]? + (switchNotices x.T x.others).size := by
  subst hn hc
  obtain ⟨t1, t2⟩ := hts
  rw [hor] at t1 t2
  rw [oraclesAt_len hl] at t1
  rw [P1K2.told_tenants hl] at t2
  exact ⟨t1, t2⟩

/-- **WHAT IS OWED ON THE NUMBERS AT A SWITCH, JOINED.** s: the state whose book is counted. t: the
state off which the front is taken. -/
theorem debts_core {k : Nat} {b : Block St Cl}
    (hts : (N₀.atBlocks sh links bs).treesAt ps[k + 1]? =
        (N₀.atBlocks sh links bs).treesAt ps[k]? + b.oracles.flatten.length ∧
      (N₀.atBlocks sh links bs).msgsAt ps[k + 1]? =
        (N₀.atBlocks sh links bs).msgsAt ps[k]? +
          (b.oracles.flatten.map fun o => o.tenants.length).sum)
    {grp : Nat} {codes : Codes} {sent : Array OracleNotice}
    (hor : b.oracles.flatten = oraclesAt grp codes sent) {m : Nat} (hm : m ≠ 0)
    (hT : sentFitB (N₀.atBlocks sh links bs) m ps[k]? codes sent = true) {s t : S}
    (hb : bookAt (N₀.atBlocks sh links bs) ps[k]? s = true) {p : P2} {n₀ : Nat}
    (hF : Fence p sent codes n₀ t) {x : _root_.Tw.K2.Front} (hx : FrontOf p t x) {lay : TreeLay}
    (hl : layTrees x.st.codes (switchNotices x.T x.others) = some lay) {d n : Nat}
    (hk : n = (switchNotices x.T x.others).size - 1) {W : SwitchFrame} (hW : frameAt x = some W)
    (keptPos : KeptPos x.T) (hTg : x.T = ((reqGroups sh).getD m {}).target)
    (hpos : possAt bs links.length m = d)
    (hlen : (N₀.keptOf (m - 1)).length = x.T.kept.size)
    (hone : ∀ κ ∈ W.kept, (x.st.oracles.getD κ.old default).sampleRows.size = 1) :
    SwitchDebts (N₀.atBlocks sh links bs) m ps[k]? ps[k + 1]? s.book.trees.size d n x W lay := by
  obtain ⟨r1, r2⟩ := rows_debts (N₀ := N₀) (sh := sh) (links := links) (bs := bs) hm hW hTg hpos
    hlen hone
  obtain ⟨t1, t2⟩ := told_debts (N₀ := N₀) (sh := sh) (links := links) hts hor (hF x hx).1
    (hF x hx).2.1 hl
  exact switchDebts_of hT hb hF hx hl hk keptPos r1 r2 t1 t2

/-- **At a link's switch.** -/
theorem debts_link {k : Nat} {b : Block St Cl}
    (hts : (N₀.atBlocks sh links bs).treesAt ps[k + 1]? =
        (N₀.atBlocks sh links bs).treesAt ps[k]? + b.oracles.flatten.length ∧
      (N₀.atBlocks sh links bs).msgsAt ps[k + 1]? =
        (N₀.atBlocks sh links bs).msgsAt ps[k]? +
          (b.oracles.flatten.map fun o => o.tenants.length).sum)
    {grp : Nat} {codes : Codes} {sent : Array OracleNotice}
    (hor : b.oracles.flatten = oraclesAt grp codes sent) {m : Nat} (hm : m ≠ 0)
    (hT : sentFitB (N₀.atBlocks sh links bs) m ps[k]? codes sent = true) {s : S}
    (hb : bookAt (N₀.atBlocks sh links bs) ps[k]? s = true) {p : P2} {n₀ : Nat}
    (hF : Fence p sent codes n₀ s) {x : _root_.Tw.K2.Front} (hx : FrontOf p s x) {lay : TreeLay}
    (hl : layTrees x.st.codes (switchNotices x.T x.others) = some lay) {d : Nat}
    {W : SwitchFrame} (hW : frameAt x = some W)
    (keptPos : KeptPos x.T) (hTg : x.T = ((reqGroups sh).getD m {}).target)
    (hpos : possAt bs links.length m = d)
    (hlen : (N₀.keptOf (m - 1)).length = x.T.kept.size)
    (hone : ∀ κ ∈ W.kept, (x.st.oracles.getD κ.old default).sampleRows.size = 1) :
    LinkDebts (N₀.atBlocks sh links bs) m ps[k]? ps[k + 1]? s d x W lay := by
  obtain ⟨r1, r2⟩ := rows_debts (N₀ := N₀) (sh := sh) (links := links) (bs := bs) hm hW hTg hpos
    hlen hone
  obtain ⟨t1, t2⟩ := told_debts (N₀ := N₀) (sh := sh) (links := links) hts hor (hF x hx).1
    (hF x hx).2.1 hl
  exact linkDebts_of hT hb hF hx hl keptPos r1 r2 t1 t2

/-- **At the head's switch**: as many messages join the group as at a link's. -/
theorem debts_head {k : Nat} {b : Block St Cl}
    (hts : (N₀.atBlocks sh links bs).treesAt ps[k + 1]? =
        (N₀.atBlocks sh links bs).treesAt ps[k]? + b.oracles.flatten.length ∧
      (N₀.atBlocks sh links bs).msgsAt ps[k + 1]? =
        (N₀.atBlocks sh links bs).msgsAt ps[k]? +
          (b.oracles.flatten.map fun o => o.tenants.length).sum)
    {grp : Nat} {codes : Codes} {sent : Array OracleNotice}
    (hor : b.oracles.flatten = oraclesAt grp codes sent) {m : Nat} (hm : m ≠ 0)
    (hT : sentFitB (N₀.atBlocks sh links bs) m ps[k]? codes sent = true) {s t : S}
    (hb : bookAt (N₀.atBlocks sh links bs) ps[k]? s = true) {p : P2} {n₀ : Nat}
    (hF : Fence p sent codes n₀ t) {x : _root_.Tw.K2.Front} (hx : FrontOf p t x) {lay : TreeLay}
    (hl : layTrees x.st.codes (switchNotices x.T x.others) = some lay) {d : Nat}
    {W : SwitchFrame} (hW : frameAt x = some W)
    (keptPos : KeptPos x.T) (hTg : x.T = ((reqGroups sh).getD m {}).target)
    (hpos : possAt bs links.length m = d)
    (hlen : (N₀.keptOf (m - 1)).length = x.T.kept.size)
    (hone : ∀ κ ∈ W.kept, (x.st.oracles.getD κ.old default).sampleRows.size = 1) :
    SwitchDebts (N₀.atBlocks sh links bs) m ps[k]? ps[k + 1]? s.book.trees.size d
      (1 + x.T.kept.size + x.own.length) x W lay :=
  debts_core hts hor hm hT hb hF hx hl (count_of_front hx) hW keptPos hTg hpos hlen hone

/-- **At the finish's switch**: t: the state behind the way in; the link's own messages are none. -/
theorem debts_finish {k : Nat} {b : Block St Cl}
    (hts : (N₀.atBlocks sh links bs).treesAt ps[k + 1]? =
        (N₀.atBlocks sh links bs).treesAt ps[k]? + b.oracles.flatten.length ∧
      (N₀.atBlocks sh links bs).msgsAt ps[k + 1]? =
        (N₀.atBlocks sh links bs).msgsAt ps[k]? +
          (b.oracles.flatten.map fun o => o.tenants.length).sum)
    {grp : Nat} {codes : Codes} {sent : Array OracleNotice}
    (hor : b.oracles.flatten = oraclesAt grp codes sent) {m : Nat} (hm : m ≠ 0)
    (hT : sentFitB (N₀.atBlocks sh links bs) m ps[k]? codes sent = true) {s t : S}
    (hb : bookAt (N₀.atBlocks sh links bs) ps[k]? s = true) {p : P2} (hp : p.stands = .finish)
    {n₀ : Nat}
    (hF : Fence p sent codes n₀ t) {x : _root_.Tw.K2.Front} (hx : FrontOf p t x) {lay : TreeLay}
    (hl : layTrees x.st.codes (switchNotices x.T x.others) = some lay) {d : Nat}
    {W : SwitchFrame} (hW : frameAt x = some W)
    (keptPos : KeptPos x.T) (hTg : x.T = ((reqGroups sh).getD m {}).target)
    (hpos : possAt bs links.length m = d)
    (hlen : (N₀.keptOf (m - 1)).length = x.T.kept.size)
    (hone : ∀ κ ∈ W.kept, (x.st.oracles.getD κ.old default).sampleRows.size = 1) :
    SwitchDebts (N₀.atBlocks sh links bs) m ps[k]? ps[k + 1]? s.book.trees.size d
      (1 + x.T.kept.size) x W lay :=
  debts_core hts hor hm hT hb hF hx hl (count_finish hp hx) hW keptPos hTg hpos hlen hone

end

end VerifiableInference.Desc.First.K2

#print axioms VerifiableInference.Desc.First.K2.debts_head
#print axioms VerifiableInference.Desc.First.K2.debts_finish

#print axioms VerifiableInference.Desc.First.K2.told_debts
#print axioms VerifiableInference.Desc.First.K2.debts_core
#print axioms VerifiableInference.Desc.First.K2.debts_link
