-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Johnson/RunOne/Law/K12Back29.lean: The key file's
tables, row 2.9 (the proximity test on the folded row's group G_u): THE LAST JOIN OF THE WAY BACK:
the premise «law» of `relAt_back_to` (KeyQuietSub.lean) OFF THE VERY ANTECEDENTS THAT `Pays` HANDS
ITS PAYER (K12AtField.lean: its last clause): the promise in front · the sub-protocol's piece puts
out y at x · the game's conclusion at the seat's two doors. Statements; each proof is a few calls.
WHAT IT IS NOT, FIRST. THE PROMISE BEHIND (on₂ … 10 y: that clause's first half) IS NOT TOUCHED: it
is fwd_29_name (K12FwdName.lean). WITHOUT IT `Pays` IS NOT HAD, WHATEVER THIS FILE GIVES. It pays no
field of the tables. No soundness is claimed. Nothing on hiding.
  `law_29_coreL`: `law_29_coreF` (K12Law29Core.lean) with `CoreFacts` replaced by `CoreLeft`
    (Johnson/Desc/K12/Coin/CoreBehindQ.lean): six clauses of the bundle fall to the «accept» that
    the relation QW holds, under johOk and planOk.
  `back_29`: the same conclusion; QW is made of the piece's «accept» (`qw_of_yes`, GameOut.lean);
    that the riding member's out-of-domain (OOD) sample and committed word stay across the test is
    had of the same «accept» (`riding_stays₂`, K12RidingStays.lean).
BESIDE THEM: `law_29_coreM` · `back_29M`: «left» MEMBER BY MEMBER (`MemberLeft`,
Johnson/Desc/K12/Coin/MemberAtYes.lean), at any numbering by labels nl: the two «accept»s are handed
to its payer; «the first tree is 0» and `guard_29` fall out. hb · hal are
other files' to pay (by report); hi · hSm · hlog · told · h1 h2 lie in scope in
KeyAt2932Scope.lean [W]. EVERY BINDER OF back_29, ITS OWNER AND ITS STATE
([W]: by report, not shown here):
  hb · hal: the piece holds the seat's sub-protocol. OWNER: K12's files (nine_facts_key: not in this
    library) · K12AtField.lean (U_at). STATE: typed apart; the tie of the two forms is nobody's.
  hp · hj · hft: tests on the place: planOk · johOk · the first tree is 0. OWNER: K12's files on the
    places and on the sizes. STATE: typed at the made places [W].
  hout · hq · hon: the three antecedents of Pays' last clause. OWNER: the caller. STATE: had.
  left: CoreLeft at the verifier's state behind the door in. OWNER: K12's files · the files of
    Johnson/Desc/Sound/ · the shared chain's files. STATE: UNPAID AS A WHOLE.
  hi: LayIdem. OWNER: the tables' files (layIdem_h₂, KeyFillBase.lean). STATE: paid [W].
  hlog · told: the two trees' depths; the trees are told. OWNER: SeamDesc.lean (depth_of_planOk) ·
    the tables' files. STATE: typed [W].
  hsm: the OOD seeds' tie at the two members. OWNER: GoodSendForms.lean (smpAt_of) · the tables'
    files · other files. STATE: typed apart [W].
  hsh: every leaf is shown. OWNER: the tables' files (Free₂.shown, a part of hon, in the tables'
    form). STATE: the tie of that form to Sound.ShownAt: not looked at here.
  hmem0 · hmem3 · hrd: the filler's letters. OWNER: whoever fills mem and rd. STATE: free.
  hK: no open row is marked as a sample row. OWNER: the tables' files (openKinds_at_reached₂ :
    Hist₂ … ⊢ OpenKinds). STATE: the payer is typed [its statement read]; Hist₂ is no part of on₂:
    it stands beside it in the tables' own promise On₂′ (KeyTablesR.lean:45 [read]).
  hgrp · h1 h2: the group's members and the count of its open rows. OWNER: the tables' files
    (shape₂) · KeySplitShape.lean (two_at_scope). STATE: in part [W].
  x0 hx hsmd hss: message 0 is sampled and has sample rows. OWNER: the tables' files (Free₂) · the
    test's own «accept». STATE: typed apart.
  hSm · hlt · hbase: the reading's OOD sample reads the state's rows alone · the riding message is
    there and is not the first mask · its tree lies below the piece's base. OWNER: other files · the
    tables' files · K12's files on the seats. STATE: in part [W].

-/
import Johnson.RunOne.Law.K12Law29Core
import Johnson.RunOne.Law.K12RidingStays
import Johnson.Desc.K12.Coin.MemberAtYes

set_option autoImplicit false
set_option relaxedAutoImplicit false

noncomputable section

namespace Johnson.RunOne.Law.K12Back29
open OnBytes OnBytes.Params OnBytes.Slice
open VerifiableInference.Desc VerifiableInference.Desc.Key VerifiableInference.Desc.Key.Fill
open VerifiableInference.Desc.K12 VerifiableInference.Desc.K12.Coin
open VerifiableInference.Desc.Sound (Frame strsOf Piece held)
open Cb Johnson.Pack OnBytes.Maker
open _root_.Run (ckP)
open Johnson.Top.H (csKey)
open Johnson.RunOne Johnson.RunOne.KeyRows23
open LPFD.CandLaid
open H2K.Pin (tabP NTuple)
open H2K.Pub (johOk)
open Johnson.RunOne.Law.K12TupleOfCore Johnson.RunOne.Law.K12Law29Core

variable {XI Cells Rec : Type} (F : FileDescription XI) (Fr₂ : Frame)
  (decT : (ℕ → Option (ℕ × List UInt64)) → Rec → Option Cells)
  (recOf : VerifiableInference.Desc.Key.Xi → Option Rec) (orc₁ : ℕ → Option ℕ)
  (tab : Cells → ℕ → ℕ → OnBytes.F) (S : LinShape) (K₁ : KPlan)
  (enc : (Nat → E) → Nat → E) (rad a : Nat) (coll : Strs → Rec → Prop)
  (last₁ : VerifiableInference.Desc.Key.FirstState → Bool) (off₂ : Nat → Nat)

/-- **`law_29_coreF`, asking of the seam's bundle only what the relation's own «accept» does not
give.** -/
theorem law_29_coreL (π : P12) (lo : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₂ × St₂) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (x y : (P₂ × St₂) × Fr₂.E.Str)
    (hQ : QW Fr₂ π (nlAt π lo) r rdN (Seat.enter (·.gU) (·.firstMask)) Seat.leave x y)
    (hft : π.nums.firstTree = 0)
    (hon : on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a coll last₁ off₂ 9 x)
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (left : ∀ t, Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t →
      CoreLeft csKey F Fr₂ π (fun z => lo + z) (fun s => r s.st) smp mem
        (fun z => z = ⟨sixS, i3⟩ ∨ z = ⟨sixS, i5⟩) t x.2 x.1 (strsOf Fr₂ x.2))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hlog : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ x.2) i)
    (hmem0 : mem 0 = some ⟨sixS, i3⟩) (hmem3 : mem 3 = some ⟨sixS, i5⟩)
    (hK : Means.OpenKinds x.1.2.st)
    (hgrp : ∀ G0, x.1.2.st.groups[x.1.2.loc.gU]? = some G0 →
      (∀ o ∈ G0.members.toList, o = 0 ∨ o = 3) ∧ 0 ∈ G0.members.toList ∧
        S.fold.index.answers + S.fold.columns + 1 ≤ G0.rows.size)
    (h1 : S.fold.index.answers ≠ 0) (h2 : S.fold.columns ≠ 0) (x0 : OnBytes.Oracle)
    (hx : x.1.2.st.oracles[0]? = some x0) (hsmd : x0.sampled = true)
    (hss : x0.sampleRows.size ≠ 0)
    (hsmp : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp y.1 (atSix 5).1
        (atSix 5).2 =
      (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp x.1 (atSix 5).1
        (atSix 5).2)
    (hword : wordOf F (strsOf Fr₂ y.2) (atSix 5).1 (atSix 5).2 =
      wordOf F (strsOf Fr₂ x.2) (atSix 5).1 (atSix 5).2) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
      rw.ins = [KItem.claim 2 "record", .claim 2 "columns", .claim 2 "FoldU", .srow 3, .pin 3] →
      KItem.pin 5 ∈ rw.outs ++ rw.ctx →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) y.1
          (strsOf Fr₂ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) x.1
          (strsOf Fr₂ x.2) (layAt atSix [3] tbl w) := by
  obtain ⟨t0, tE, h1', _, _, rs, gs, hy⟩ := id hQ
  exact law_29_coreF F Fr₂ decT recOf orc₁ tab S K₁ enc rad a coll last₁ off₂ π lo r rdN smp mem rd
    hrd x y hQ hft hon
    (fun t ht => by
      obtain rfl : t0 = t := Except.ok.inj (h1'.symm.trans ht)
      exact coreFacts_of_yes csKey F Fr₂ π _ r smp mem _ t0 tE x.2 x.1 (strsOf Fr₂ x.2) hj
        (H2K.JointK.early_of_planOk π hp) hp rs gs hy (left t0 ht))
    hi hlog told hsm hsh hmem0 hmem3 hK hgrp h1 h2 x0 hx hsmd hss hsmp hword

/-- **Row 2.9's «law», off the antecedents of `Pays`' last clause.** -/
theorem back_29 {Cl W : Type} (π : P12) (lo : ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₂ × St₂) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (p : Piece (ckP .two) Fr₂ (P₂ × St₂) Cl W) (B : Block St₂ Cl) (hb : p.b = held B)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside
      (Seat.enter (·.gU) (·.firstMask)) Seat.leave) B)
    (x y : (P₂ × St₂) × Fr₂.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out x τ = some y)
    (hq : ∃ t t', Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t ∧
      (Seat.leave x.1.2 t' = .ok y.1.2 ∧ y.1.1 = x.1.1) ∧
      QN π (NTuple Fr₂ π (nuOf π (nlAt π lo) t) (fun s => r s.st) rdN) (t, x.2))
    (hft : π.nums.firstTree = 0)
    (hon : on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a coll last₁ off₂ 9 x)
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (left : ∀ t, Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t →
      CoreLeft csKey F Fr₂ π (fun z => lo + z) (fun s => r s.st) smp mem
        (fun z => z = ⟨sixS, i3⟩ ∨ z = ⟨sixS, i5⟩) t x.2 x.1 (strsOf Fr₂ x.2))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hlog : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ x.2) i)
    (hmem0 : mem 0 = some ⟨sixS, i3⟩) (hmem3 : mem 3 = some ⟨sixS, i5⟩)
    (hK : Means.OpenKinds x.1.2.st)
    (hgrp : ∀ G0, x.1.2.st.groups[x.1.2.loc.gU]? = some G0 →
      (∀ o ∈ G0.members.toList, o = 0 ∨ o = 3) ∧ 0 ∈ G0.members.toList ∧
        S.fold.index.answers + S.fold.columns + 1 ≤ G0.rows.size)
    (h1 : S.fold.index.answers ≠ 0) (h2 : S.fold.columns ≠ 0) (x0 : OnBytes.Oracle)
    (hx : x.1.2.st.oracles[0]? = some x0) (hsmd : x0.sampled = true)
    (hss : x0.sampleRows.size ≠ 0)
    (hSm : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).SmOnly)
    (hlt : ∀ o, orc₂ ((baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).arr
      (atSix 5).1 (atSix 5).2) = some o →
      o < x.1.2.st.oracles.size ∧ x.1.2.loc.firstMask ≠ some o)
    (hbase : (atSix 5).1 < p.base) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
      rw.ins = [KItem.claim 2 "record", .claim 2 "columns", .claim 2 "FoldU", .srow 3, .pin 3] →
      KItem.pin 5 ∈ rw.outs ++ rw.ctx →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) y.1
          (strsOf Fr₂ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) x.1
          (strsOf Fr₂ x.2) (layAt atSix [3] tbl w) := by
  obtain ⟨t, t', e1, ⟨e2, _⟩, e3⟩ := hq
  obtain ⟨hsmp, hword⟩ := K12RidingStays.riding_stays₂
    (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁) F Fr₂ hSm (·.gU)
    (·.firstMask) π (H2K.JointK.early_of_planOk π hp) (H2K.JointK.answers_of_planOk π hp) p B hb
    hal x y τ hout (atSix 5).1 (atSix 5).2 hlt hbase
  exact law_29_coreL F Fr₂ decT recOf orc₁ tab S K₁ enc rad a coll last₁ off₂ π lo r rdN smp mem rd
    hrd x y (qw_of_yes π (nlAt π lo) r rdN _ _ p B hb hal x y τ hout ⟨t, t', e1, e2, e3⟩) hft hon hj
    hp left hi hlog told hsm hsh hmem0 hmem3 hK hgrp h1 h2 x0 hx hsmd hss hsmp hword

/-! ## «left», member by member -/

/-- **`law_29_coreF`'s conclusion with the seam's bundle paid member by member**
(`core_behind_QWm`,
Johnson/Desc/K12/Coin/MemberAtYes.lean · `law_29_of_core`, K12Law29Core.lean): AT ANY NUMBERING BY
LABELS nl. Against `law_29_coreL`: `CoreLeft` ↦ at whatever the state behind the door in fixes: the
codes' equation and an injective list of members, holding the group's two, with `MemberLeft` at
each, at no := nuOf π nl t · «the place's first tree is 0» AND `guard_29` FALL OUT: nothing is
carried to the book's places. FIRST LIMIT: the book's price stands in MemberLeft's last clause (the
word at that no). -/
theorem law_29_coreM (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₂ × St₂) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (x y : (P₂ × St₂) × Fr₂.E.Str)
    (hQ : QW Fr₂ π nl r rdN (Seat.enter (·.gU) (·.firstMask)) Seat.leave x y)
    (hon : on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a coll last₁ off₂ 9 x)
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (left : ∀ t, Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain),
      Fixes π t s rest G0 Ly D →
      D.st.codes = csKey ∧
      ∃ (xs : Fin D.mems.length → Sound.Mem) (es : Fin D.mems.length → ℕ),
        Function.Injective xs ∧
        (∀ z, z = ⟨sixS, i3⟩ ∨ z = ⟨sixS, i5⟩ → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length,
          MemberLeft csKey F Fr₂ (nuOf π nl t) (fun q => r q.st) smp mem x.2 x.1
            (strsOf Fr₂ x.2) s D j (xs j) (es j))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hlog : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ x.2) i)
    (hmem0 : mem 0 = some ⟨sixS, i3⟩) (hmem3 : mem 3 = some ⟨sixS, i5⟩)
    (hK : Means.OpenKinds x.1.2.st)
    (hgrp : ∀ G0, x.1.2.st.groups[x.1.2.loc.gU]? = some G0 →
      (∀ o ∈ G0.members.toList, o = 0 ∨ o = 3) ∧ 0 ∈ G0.members.toList ∧
        S.fold.index.answers + S.fold.columns + 1 ≤ G0.rows.size)
    (h1 : S.fold.index.answers ≠ 0) (h2 : S.fold.columns ≠ 0) (x0 : OnBytes.Oracle)
    (hx : x.1.2.st.oracles[0]? = some x0) (hsmd : x0.sampled = true)
    (hss : x0.sampleRows.size ≠ 0)
    (hsmp : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp y.1 (atSix 5).1
        (atSix 5).2 =
      (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂.smp x.1 (atSix 5).1
        (atSix 5).2)
    (hword : wordOf F (strsOf Fr₂ y.2) (atSix 5).1 (atSix 5).2 =
      wordOf F (strsOf Fr₂ x.2) (atSix 5).1 (atSix 5).2) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
      rw.ins = [KItem.claim 2 "record", .claim 2 "columns", .claim 2 "FoldU", .srow 3, .pin 3] →
      KItem.pin 5 ∈ rw.outs ++ rw.ctx →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) y.1
          (strsOf Fr₂ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) x.1
          (strsOf Fr₂ x.2) (layAt atSix [3] tbl w) := by
  obtain ⟨_, _, hfree, _⟩ := id (hon.resolve_left (fun h => h trivial))
  exact law_29_of_core F Fr₂ decT recOf orc₁ tab S K₁ enc rad a coll last₁ off₂ smp mem rd hrd x y
    hon
    (core_behind_QWm csKey F Fr₂ π nl r rdN smp mem _ rd hrd _ _ x y x.1 (strsOf Fr₂ x.2) hQ hj hp
      left (fun t ht => by cases ht; exact hfree.order))
    hi hlog told hsm hsh hmem0 hmem3 hK hgrp h1 h2 x0 hx hsmd hss hsmp hword

/-- **Row 2.9's «law», off the antecedents of `Pays`' last clause, with «left» member by
member.** `back_29`'s like over `law_29_coreM`; at any numbering by labels nl. -/
theorem back_29M {Cl W : Type} (π : P12) (nl : ℕ → ℕ) (r : Fmt.M1.Stage → ℕ) (rdN : ℕ → ℕ)
    (smp : (P₂ × St₂) → (s : Sound.Sending) → (i : Fin s.l.length) →
      Option ((sigOf csKey s.l).om i).Smp)
    (mem : ℕ → Option Sound.Mem)
    (rd : (x : Sound.Mem) → ((sigOf csKey x.1.l).om x.2).Msg → OnBytes.Part → ℕ → GE)
    (hrd : ∀ x m part i, rd x m part i = tabP csKey (x.1.l.get x.2).1 m part i)
    (p : Piece (ckP .two) Fr₂ (P₂ × St₂) Cl W) (B : Block St₂ Cl) (hb : p.b = held B)
    (hal : Alike ((proximityTestKind guardedProximityTestParts π : Block T12 Unit).inside
      (Seat.enter (·.gU) (·.firstMask)) Seat.leave) B)
    (x y : (P₂ × St₂) × Fr₂.E.Str) (τ : Iop.Tr (uLT (ckP .two) p.ds))
    (hout : p.ior.red.out x τ = some y)
    (hq : ∃ t t', Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t ∧
      (Seat.leave x.1.2 t' = .ok y.1.2 ∧ y.1.1 = x.1.1) ∧
      QN π (NTuple Fr₂ π (nuOf π nl t) (fun s => r s.st) rdN) (t, x.2))
    (hon : on₂ F Fr₂ (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix S K₁
      (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad a coll last₁ off₂ 9 x)
    (hj : johOk π r = true) (hp : (proximityTestKind guardedProximityTestParts π : Block T12 Unit).planOk = true)
    (left : ∀ t, Seat.enter (·.gU) (·.firstMask) x.1.2 = .ok t → ∀ (s : Fmt.M1.Stage)
      (rest : List Fmt.M1.Stage) (G0 : OnBytes.Group) (Ly : OnBytes.GroupLayout)
      (D : H2K.First.Plain),
      Fixes π t s rest G0 Ly D →
      D.st.codes = csKey ∧
      ∃ (xs : Fin D.mems.length → Sound.Mem) (es : Fin D.mems.length → ℕ),
        Function.Injective xs ∧
        (∀ z, z = ⟨sixS, i3⟩ ∨ z = ⟨sixS, i5⟩ → ∃ j, xs j = z) ∧
        ∀ j : Fin D.mems.length,
          MemberLeft csKey F Fr₂ (nuOf π nl t) (fun q => r q.st) smp mem x.2 x.1
            (strsOf Fr₂ x.2) s D j (xs j) (es j))
    (hi : LayIdem (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂)
    (hlog : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ o,
      F.oracleAt (seatAt six numSix atSix i).1 = some o → o.logLength = aOf csKey (six.get i).1)
    (told : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
      (F.oracleAt (seatAt six numSix atSix i).1).isSome = true)
    (hsm : ∀ i : Fin six.length, i = i3 ∨ i = i5 → ∀ σ : (OmAt csKey six i).Smp,
      smp x.1 sixS i = some σ → ∃ ρ : (OmAt csKey six i).Z.D,
        (OmAt csKey six i).Z.val σ.1 = (OmAt csKey six i).Z.val ρ ∧
        seedIsS csKey six numSix (rowIsK csKey six) (src₂ orc₁) i x.1 ρ σ.2)
    (hsh : ∀ i : Fin six.length, i = i3 ∨ i = i5 →
      Sound.ShownAt F csKey six (seatAt six numSix atSix) (strsOf Fr₂ x.2) i)
    (hmem0 : mem 0 = some ⟨sixS, i3⟩) (hmem3 : mem 3 = some ⟨sixS, i5⟩)
    (hK : Means.OpenKinds x.1.2.st)
    (hgrp : ∀ G0, x.1.2.st.groups[x.1.2.loc.gU]? = some G0 →
      (∀ o ∈ G0.members.toList, o = 0 ∨ o = 3) ∧ 0 ∈ G0.members.toList ∧
        S.fold.index.answers + S.fold.columns + 1 ≤ G0.rows.size)
    (h1 : S.fold.index.answers ≠ 0) (h2 : S.fold.columns ≠ 0) (x0 : OnBytes.Oracle)
    (hx : x.1.2.st.oracles[0]? = some x0) (hsmd : x0.sampled = true)
    (hss : x0.sampleRows.size ≠ 0)
    (hSm : (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).SmOnly)
    (hlt : ∀ o, orc₂ ((baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).arr
      (atSix 5).1 (atSix 5).2) = some o →
      o < x.1.2.st.oracles.size ∧ x.1.2.loc.firstMask ≠ some o)
    (hbase : (atSix 5).1 < p.base) :
    ∃ tbl : ℕ → Fill.Tab, ∀ (rw : KRow) (w : Wit Cells Unit Fill.Tab),
      rw.ins = [KItem.claim 2 "record", .claim 2 "columns", .claim 2 "FoldU", .srow 3, .pin 3] →
      KItem.pin 5 ∈ rw.outs ++ rw.ctx →
      (∀ i ∈ rw.outs ++ rw.ctx,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) y.1
          (strsOf Fr₂ y.2) w) →
      ∀ i ∈ rw.ins,
        i.holds F (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁).h₂ atSix
          (meaning₂ S K₁ (kreadFam (Cells := Cells) csKey six numSix atSix tab) enc rad) x.1
          (strsOf Fr₂ x.2) (layAt atSix [3] tbl w) := by
  obtain ⟨t, t', e1, ⟨e2, _⟩, e3⟩ := hq
  obtain ⟨hsmp, hword⟩ := K12RidingStays.riding_stays₂
    (baseK (Cells := Cells) csKey six numSix atSix decT recOf orc₁) F Fr₂ hSm (·.gU)
    (·.firstMask) π (H2K.JointK.early_of_planOk π hp) (H2K.JointK.answers_of_planOk π hp) p B hb
    hal x y τ hout (atSix 5).1 (atSix 5).2 hlt hbase
  exact law_29_coreM F Fr₂ decT recOf orc₁ tab S K₁ enc rad a coll last₁ off₂ π nl r rdN smp mem rd
    hrd x y (qw_of_yes π nl r rdN _ _ p B hb hal x y τ hout ⟨t, t', e1, e2, e3⟩) hon hj hp left hi
    hlog told hsm hsh hmem0 hmem3 hK hgrp h1 h2 x0 hx hsmd hss hsmp hword

end Johnson.RunOne.Law.K12Back29

#print axioms Johnson.RunOne.Law.K12Back29.law_29_coreL
#print axioms Johnson.RunOne.Law.K12Back29.back_29
#print axioms Johnson.RunOne.Law.K12Back29.law_29_coreM
#print axioms Johnson.RunOne.Law.K12Back29.back_29M
