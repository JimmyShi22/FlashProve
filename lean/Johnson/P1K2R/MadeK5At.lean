-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/P1K2R/MadeK5At.lean: code switching (K2): THE LAST TWO OF THE MAKINGS THAT ITS SHARE OF e₁
ASKS AT AN ATTENTION LINK's FIRST PLACE (hMade, Johnson/P1K2R/SharesAtE.lean): THE PUBLIC ITEMS
"K5.liveReq" AND "K5.readsThere", in hMade's own letters: THE FIRST PAID OUT OF TWO FACTS ON THE
STATE IN FRONT; THE SECOND BROUGHT TO NAMED PREMISES: two closed Bools on the plan, one equation
at the state in front, one Bool at the state that the switch leaves. A JOIN of
Johnson/Top/H0/Walk/FrameOpenedK5.lean with what the switch leaves. NO BLOCK IMPORTS THIS FILE.
  born_at          the group's «born» at l of reqGroups sh, read with the default, is
                   H2K5.Door.bornOf sh l
  live_left        WHAT THE SWITCH LEAVES, 1: behind an accept of the kind's decision in a link's
                   dress: liveFrontB (bornOf sh l) l m.check = true, where in front the frame's
                   shape is sh and its groups are reqGroups of its shape. By K2.yes_link_next |
                   yes_link_stays (Tw/K2C/LinkStays.lean)
  yes_link_rows    WHAT THE SWITCH LEAVES, 2: m.check.rows = s.check.rows (the text's firstKept
                   writes the frame, the numbers sent, «in a link» and the count of moments alone)
  r2B · r3B        the second and the third clause of H2K5.Door.readsAtB, with the frame's link
                   and shape as letters
  reads_left       WHAT THE SWITCH LEAVES, 3: readsFrontB W own P m.check m.book = true FROM:
                   W.A[P.l / 2]? = some q · c1 (the plan's ledger's tree q.iU3 has one row and
                   q.nW columns: ON THE PLAN ALONE) · c2 : r2B at the layout that the state behind
                   holds · c3 : r3B at the frame and the book behind
  made_k5_first    the two items behind every accept of an attention link's first place
PREMISES THAT STAY, BY NAME: ON THE STATE IN FRONT: hsh · hgr · hlk (the frame's shape is the
public data's; its groups are reqGroups of it; its link is l: SwState (K2C/DebtsState.lean) has all
three at the 25 borders, in scope) · hlay (the layout that the state holds is lay₀: that it is the
plan's since the start is said by nobody yet)
(Where this and lean/THEOREM.md differ, the page
holds.) · ON THE PLAN: ha · hatt · hsub · hW · c1 · c2 (r2B
at lay₀: a closed Bool) · ON THE STATE THAT THE SWITCH LEAVES: c3 (THE LONG ONE: the link's first
masked message has a number in the frame behind, the book behind places it, and the public data's
list of the link's own seats holds that seat).
LIMITS. "K5.readsThere" IS NOT PAID: c3 is the debt, moved and cut; hlay | c1 | c2 are shown at no
value. No soundness is claimed.
-/
import Johnson.P1K2R.MadeLookAt
import Johnson.Top.H0.Walk.FrameOpenedK5
import Johnson.Top.H0.Tw.K2C.LinkStays

set_option autoImplicit false
set_option relaxedAutoImplicit false

attribute [-instance] Inst.Model.Scl.ref

namespace P1K2
open OnBytes OnBytes.Model
open VerifiableInference.Desc (Block Place OpenedColumn KindName)
open VerifiableInference.Desc.First (S ModelPart Numbers Pub PubData pubAll)
open VerifiableInference.Desc.First.K2 (P2 decideWith k2_step_two yes_link_next yes_link_stays)
open Johnson.Desc.First.Walk (AttPar startFork)
open Johnson.Desc.First.Walk.Seat (framesOf_arms pubOf)
open Johnson.Desc.First.Walk.Tied (liveFrontB readsFrontB made_liveReq made_readsThere)
open H2K5.Door (bornOf readsAtB)
open H2K.JointK (Sits)
open ProofFile (Cl)
open IM (Hands XK Yes linksW placesW subW k2P Joined)
open _root_.Tw.K2 (sendByL8)

theorem born_at (sh : Params.ReqShape) (l : Nat) :
    ((reqGroups sh).getD l {}).born = bornOf sh l := by
  unfold bornOf
  rw [Array.getD_eq_getD_getElem?]
  cases (reqGroups sh)[l]? <;> rfl

theorem live_left {p : P2} {s m : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hp : p.stands = .link) (hd : decideWith sendByL8 p s rs gs = .ok m) {sh : Params.ReqShape}
    (hsh : s.check.frame.shape = sh) (hgr : s.check.frame.groups = reqGroups s.check.frame.shape)
    (l : Nat) : liveFrontB (bornOf sh l) l m.check = true := by
  obtain ⟨hn, _⟩ := yes_link_next hp hd
  obtain ⟨_, _, hg⟩ := yes_link_stays hp hd
  unfold liveFrontB
  rw [hn, hg, hgr, hsh, born_at]
  simp

/-- The switch in a link's dress leaves the layout by which a link's equation becomes a row. -/
theorem yes_link_rows {p : P2} {s m : S} {rs : List Fmt.RoundView} {gs : List (List (Nat × List UInt64))}
    (hp : p.stands = .link) (hd : decideWith sendByL8 p s rs gs = .ok m) :
    m.check.rows = s.check.rows := by
  obtain ⟨r₁, r₂, x, w, roots, S', f, mine, rfl, k⟩ :=
    VerifiableInference.Desc.First.K2.link_inv hp hd
  rw [k.hOut]
  rfl

/-- readsAtB's second clause, the frame's link and shape as letters. -/
def r2B (lay : Params.ReqLayout) (sh : Params.ReqShape) (l : Nat) (A : Array (Nat × String))
    (iU3 nW : Nat) : Bool :=
  (A[iU3]?).any fun b =>
    (reqArray lay b.1 b.2).any fun Ar =>
      (b.1 == l &&
        match (sh.link[b.1]?).bind fun k => k.messages[Ar.message]? with
        | some x => x.moment == 1
        | none => false) && Decidable.decide (0 < Ar.sizeI) && Decidable.decide (nW ≤ Ar.sizeC)

/-- readsAtB's third clause, the frame's link and shape as letters. -/
def r3B (own : List (Nat × Nat)) (sh : Params.ReqShape) (l : Nat) (f : ReqFrame)
    (book : TreeBook) : Bool :=
  (((((sh.link[l]?.map (·.messages)).getD []).findIdx? fun x =>
      x.shape.maskRows != 0).bind fun μ => f.whereIs l μ).bind fun o =>
    (book.place[o]?).bind fun x => if own.contains x then some x else none).isSome

theorem reads_left {W : Verify.Public} {own : List (Nat × Nat)} {P : AttPar} {m : S}
    {sh : Params.ReqShape} (hsh : m.check.frame.shape = sh) (hlk : m.check.frame.link = P.l)
    {q : Attention.Plan} (hW : W.A[P.l / 2]? = some q)
    (c1 : ((startFork P.X P.ns).trees[q.iU3]?).any (fun T => T.R == 1 && T.K == q.nW) = true)
    (c2 : r2B m.check.rows.layout sh P.l P.X.arrayOf q.iU3 q.nW = true)
    (c3 : r3B own sh P.l m.check.frame m.book = true) :
    readsFrontB W own P m.check m.book = true := by
  unfold readsFrontB
  rw [hW]
  show readsAtB own q.iU3 q.nW _ _ m.book = true
  unfold readsAtB
  dsimp only
  unfold r2B at c2
  unfold r3B at c3
  rw [hsh, hlk, c1, Bool.true_and, Bool.and_eq_true]
  exact ⟨c2, c3⟩

variable {Q : Type}

theorem made_k5_first {Z : ProofFile.Pub} {G₀ : ProofFile.Ground} {l : Nat} (h1 : 1 ≤ l) (h24 : l < 24)
    {b b' : Block S Cl} (hlot : ∃ L ∈ ProofFile.onlineFirstChainBlockTables Z, b' ∈ L.blocks G₀)
    (hpl : b'.place = { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hJ : Joined Z l b b' { chain := 1, link := some l, piece := 1, kind := .K2 })
    (hsub : (ProofFile.subsOf Z)[l]? = some (subW l)) (hatt : subW l = .attention)
    (D : PubData) (base : Pub → Q × S → Bool) (z : Q) (ha : D.d5.isAtt l = true)
    {q : Attention.Plan} (hW : D.d5.W.A[l / 2]? = some q)
    (c1 : ∀ X p, Z.p.built.links[l]? = some X → X.kind = 1 → Z.p.X.A[X.g]? = some p →
      ((startFork (pubOf X) p.ns).trees[q.iU3]?).any (fun T => T.R == 1 && T.K == q.nW) = true)
    {N : Numbers} {E : Nat → S → Bool} {ft : Nat} {s s' : S} (hy : Yes ft b s s')
    (hu : s.failed = none) (hu' : s'.failed = none)
    (hx : XK N linksW placesW E (14 * l + 2) s = true)
    (hsh : s.check.frame.shape = D.d5.shape)
    (hgr : s.check.frame.groups = reqGroups s.check.frame.shape) (hlk : s.check.frame.link = l)
    {lay₀ : Params.ReqLayout} (hlay : s.check.rows.layout = lay₀)
    (c2 : ∀ X, Z.p.built.links[l]? = some X →
      r2B lay₀ D.d5.shape l (pubOf X).arrayOf q.iU3 q.nW = true)
    (c3 : ∀ (p₂ : P2) r₁ r₂ gs m, p₂.stands = .link →
      decideWith sendByL8 p₂ s [r₁, r₂] gs = .ok m →
      r3B (D.d5.ownOf l) D.d5.shape l m.check.frame m.book = true) :
    pubAll D base (.more (some l) "K5.liveReq") (z, s') = true ∧
      pubAll D base (.more (some l) "K5.readsThere") (z, s') = true := by
  obtain ⟨L, hL, hb'⟩ := hlot
  obtain ⟨x, hx', rfl⟩ := IM.lot_K2 hL hb' (by rw [hpl])
  have hi := IM.k2_mem hx'
  rw [show x.place = _ from hpl] at hi
  rcases hi with ⟨_, hm⟩ | hd
  · obtain ⟨rs, cols, n, e⟩ := hy
    obtain ⟨fs, f, m, _, _, e3, _⟩ := hJ.step e
    exact absurd ⟨rs, cols, n, e3⟩ (never_of_mute hm s m)
  · obtain ⟨fs, f, hfs, hf, hSJ⟩ := sits_of_joined hJ (fun e => by cases e) rfl hd
    obtain ⟨Pp, n, _, _, hA⟩ := sitsJoined_keeps hfs hf hSJ
    rcases hA with ⟨l', HP, _, _, hS, _⟩ | ⟨l', _, hS, _⟩
    · have H := hands_link_other h1 h24 rfl hS (door_head_opened f HP).mark (N := N)
        (E := fun j t => if j = 14 * l + 2 + 1 then
          (pubAll D base (.more (some l) "K5.liveReq") (z, t) &&
            pubAll D base (.more (some l) "K5.readsThere") (z, t))
          else E j t) (ft := ft)
      have hx2 := H.more s s' hy hu hu' (by
        rw [xk_same (E := E)]
        · exact hx
        · exact if_neg (by omega))
      rw [if_pos rfl, Bool.and_eq_true] at hx2
      exact hx2
    · obtain ⟨rs, cols, k, e⟩ := hy
      obtain ⟨t, t', e1, e2, e3⟩ := hS.step ft s s' rs cols k e
      obtain rfl : s = t := Except.ok.inj e1
      obtain ⟨r₁, r₂, gs, _, hdc⟩ := k2_step_two e2
      have ho := leaveOpened_is e3
      obtain ⟨X₀, hX₀, hk₀, hs0, _⟩ := kinds_of_subs h24 hsub
      obtain ⟨es, el, _⟩ := yes_link_stays (p := k2P Z _ _ .link n) rfl hdc
      rcases framesOf_arms hfs hf with ⟨X, hX, hk, _⟩ | ⟨h0, _⟩ |
        ⟨_, X, p, Q', hX, hk, hA', hQ, _, eo, _⟩ | ⟨_, X, hp, Q', hX, hk, _⟩
      · obtain rfl : X₀ = X := Option.some.inj (hX₀.symm.trans hX)
        exact absurd hk hk₀
      · omega
      · rw [eo] at ho
        subst hQ
        exact ⟨made_liveReq D base ho ha z (live_left rfl hdc hsh hgr l),
          made_readsThere D base ho ha z
            (reads_left (es.trans hsh) (el.trans hlk) hW (c1 X p hX hk hA')
              (by rw [yes_link_rows (p := k2P Z _ _ .link n) rfl hdc, hlay]; exact c2 X hX)
              (c3 _ r₁ r₂ gs t' rfl hdc))⟩
      · obtain rfl : X₀ = X := Option.some.inj (hX₀.symm.trans hX)
        have := hs0 hk
        rw [hatt] at this
        cases this

end P1K2

#print axioms P1K2.live_left
#print axioms P1K2.yes_link_rows
#print axioms P1K2.reads_left
#print axioms P1K2.made_k5_first
