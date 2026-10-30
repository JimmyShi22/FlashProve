-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
Compile/Batch/CompleteChain.lean: under the hypotheses of `tri_chainT`, the verifier recomputes the
honest prover's Fiat-Shamir chain (words of this library: lean/GLOSSARY.md).

All chains of a batch (`chainT`, Compile/Batch/Prover.lean) against the chain of one slot (`recomputeChain`,
Compile/Batch/Verifier.lean), for fixed oracle functions. The store is the list of strings for which
the tokens stand (vs). A round is local (each slot has its own challenge) or shared by all slots;
the joining round is the first shared round after a local one. There each slot's chain is hashed to
a slot value, and the request tree is the Merkle tree over the slot values. The query formats (F1)
to (F5) are the constructors of `Head` (Compile/Batch/Oracles.lean).

Rounds with proof-of-work bits (`fbG`). The programs with tokens make attempt j + 1 of a search at
the ghost name `fbw t j`, whereas the scheme queries `fb t` (`realQ`). So the fixed family is
assumed to answer the ghost names as `fb t`: this is `RealFam`; `realF f`
(Compile/Batch/SpecLoop.lean) does so by definition. `tri_fbG`: whatever the search does, what
follows is run on the answer of `fb t` at the query whose plain part holds the number of the final
attempt (`putO`) (not all hypotheses are named here: see its statement). The verifier's chain is run
on the plain parts with these numbers written in (`putB`); `SlotDone` names them nJ (the slot's) and
n0s (the shared ones), in the order of the rounds. Among the hypotheses of `tri_chainT`: `RealFam`,
`RoundsQueryLayout.OKG`.

Notation: `Tri f c vs Q` (Compile/EraseKit.lean): a proposition: under the oracle functions f,
whatever the coins, the erased program c, started with the store vs, returns a value a and a store
vs' with Q a vs'; `EvalsTo f x a` (Compile/MerkleRom.lean): a proposition: under the oracle
functions f the algorithm x returns a, whatever its coins; `St lam K L α`
(Compile/Batch/TokTree.lean): `Step (spec lam K L) (split lam K L) α`: a token program (`Step`,
Rom/Defer.lean; the head of Compile/Batch/Prover.lean); `fbw t k`, a ghost name (`OracleName`,
Compile/Batch/Oracles.lean): an oracle of the analysis, which no algorithm of the scheme ever
queries; `lam`, `K`: natural numbers; a `Dig lam` (Iop/Wire.lean): a hash block (a digest or a
chaining value): lam bits; a `Blk lam K` (Compile/Batch/Prover.lean): `Fin K → Dig lam`; `L`: an
`BatchProtocol I X` (Iop/Batch.lean): the five algorithms (I, D, Test, Link, Batch), with the honest sides;
`sMT`: a natural number: the length of the salt of a leaf (Compile/Batch/Verifier.lean); `t`: a
`Tag` (Compile/Oracles.lean): test, link or onl; `cms`: a `List (Dig lam)`: the external roots
(`verifyB`, Compile/Batch/Verifier.lean); `embS`, `embP` say how symbols and plain parts are written
into queries (`verifyB`, Compile/Batch/Verifier.lean); `xin`: `Y → Option X`: `xin x` is the x of
`recomputeChain` (Compile/Batch/Verifier.lean): the whole instance (none: Test, Link); `depthReq`: a natural
number; in `QueryLayout` (Iop/BatchWire.lean): depth of a request tree: there are 2^depthReq slots; `a0`:
an `Acc0` (Compile/Batch/Prover.lean): what the shared part has accumulated; `acc`: a `SlotAcc`
(Compile/Batch/Prover.lean): what a slot has accumulated.

Limits: nothing here says that a proof-of-work check is passed.
-/
import Compile.Batch.CompleteTree
import Compile.Batch.Prover
import Iop.BatchFmt

noncomputable section

namespace Compile.Batch.Cmpl
open Iop Rom

variable {I X : Type} {lam K : ℕ} {L : BatchProtocol I X} (f : Fam (spec lam K L))

/-- the ghost names `fbw t j` are answered as `fb t` -/
def RealFam : Prop := ∀ (t : Tag) (j : ℕ) (q : FbIn lam L t), f (OracleName.fbw t j) q = f (OracleName.fb t) q

/-- the plain part with the number of the final attempt written in; unchanged where there are no
proof-of-work bits -/
def putO {C P : Type} (gr : Option (GrW C P)) (nc : Option ℕ) (α : P) : P :=
  match gr with
  | none => α
  | some g => g.put (nc.getD 0) α

/-! ## Part 1. The rounds, unfolded -/

section Unfold
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq : ℕ)
  {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A)
  (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
  (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (m0 : a.M0)
  (k0 : a.kind.Sh r.Chal → SStrat s A) (zs : List (SlotSt lam K Y (r :: s))) (a0 : Acc0)

theorem chainT_lo (hk : a.kind = .lo) (ph : PhT) :
    chainT sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i ph (m0, k0) zs a0 =
      (eachM
        (slotLo sMT t cms xin a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i ph)
        zs).bind fun zs' =>
          chainT sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
              (i + 1) ph.afterLo (k0 (a.kind.shOf (w.chal (blk0 lam K)))) zs'
              { a0 with trees := a0.trees ++ [none] } := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .lo := hk
  rfl

theorem chainT_join (hk : a.kind = .sh) :
    chainT sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i .loc (m0, k0) zs a0 =
      (joinM sMT t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i zs).bind fun o =>
          (reqT depthReq o.2).bind fun rq =>
          tree0 sMT a w (fun p => embS (.inl p)) m0 fun tr0 =>
          fbG w.gr0 w.chal t i rq.root [] (tr0.map TTree.root) (fun _ => Head.f4 cms)
              (fun _ => f4_inj cms) (fun α => embP (.inl (.inl α))) (a.pl0 m0) fun nc dd bl tl =>
          chainT sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
              (i + 1) (.shr tl) (k0 (a.kind.shOf (w.chal bl))) (o.1.map (hear w bl true))
              { trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl], req := some rq,
                nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead } := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl

theorem chainT_shr (hk : a.kind = .sh) (tk0 : Tok) :
    chainT sMT t cms xin depthReq (r :: s) (a, A) (w, W) embS embP i (.shr tk0) (m0, k0) zs a0
      = tree0 sMT a w (fun p => embS (.inl p)) m0 fun tr0 =>
          fbG w.gr0 w.chal t i tk0 [] (tr0.map TTree.root) (fun _ => Head.f5)
              (fun _ => f5_inj) (fun α => embP (.inl (.inl α))) (a.pl0 m0) fun nc dd bl tl =>
          chainT sMT t cms xin depthReq s A W (fun p => embS (.inr p)) (fun z => embP (.inr z))
              (i + 1) (.shr tl) (k0 (a.kind.shOf (w.chal bl))) (zs.map (hear w bl false))
              { a0 with
                trees := a0.trees ++ [tr0], toks := a0.toks ++ [tl],
                nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead } := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  rfl

/-- in a local round the shared strategy does not depend on the challenge -/
theorem shOf_lo (hk : a.kind = .lo) (c c' : r.Chal) : a.kind.shOf c = a.kind.shOf c' := by
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .lo := hk
  rfl

/-- `putB` does not depend on the token of the phase -/
theorem putB_shr (tk tk' : Tok) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (nJ n0 : List ℕ) (pls : Plains s),
      putB s A W (.shr tk) nJ n0 pls = putB s A W (.shr tk') nJ n0 pls
  | [], _, _, _, _, _ => rfl
  | _ :: _, (a, _), _, _, _, _ => by
      obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
      cases kind <;> rfl

/-- A local round: the slot's plain part gets the number of the final attempt, if the round has
proof-of-work bits (nc is given exactly then). -/
theorem putB_lo (hk : a.kind = .lo) (ph : PhT) (nc : Option ℕ) (hnc : nc.isSome = w.grJ.isSome)
    (nJ n0 : List ℕ) (P : Plains (r :: s)) :
    putB (r :: s) (a, A) (w, W) ph (nc.toList ++ nJ) n0 P =
      (a.plain.symm ((a.plain P.1).1, putO w.grJ nc (a.plain P.1).2),
        putB s A W ph.afterLo nJ n0 P.2) := by
  obtain ⟨pl, pls⟩ := P
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .lo := hk
  simp only [putB, putO]
  cases hg : w.grJ with
  | none =>
      rw [hg] at hnc
      cases nc with
      | none => simp
      | some m => cases hnc
  | some g =>
      rw [hg] at hnc
      cases nc with
      | none => cases hnc
      | some m => rfl

/-- A shared round in format (F4) or (F5): the shared plain part gets the number of the final
attempt, if the round has proof-of-work bits (nc is given exactly then). -/
theorem putB_sh (hk : a.kind = .sh) (ph : PhT) (hph : ph = .loc ∨ ∃ tk, ph = .shr tk) (tl : Tok)
    (nc : Option ℕ) (hnc : nc.isSome = w.gr0.isSome) (nJ n0 : List ℕ) (P : Plains (r :: s)) :
    putB (r :: s) (a, A) (w, W) ph nJ (nc.toList ++ n0) P =
      (a.plain.symm (putO w.gr0 nc (a.plain P.1).1, (a.plain P.1).2),
        putB s A W (.shr tl) nJ n0 P.2) := by
  rw [putB_shr tl 0]
  obtain ⟨pl, pls⟩ := P
  obtain ⟨kind, M0, Mj, split, P0, Pj, pl0, plj, plain, own⟩ := a
  obtain rfl : kind = .sh := hk
  cases hg : w.gr0 with
  | none =>
      rw [hg] at hnc
      cases nc with
      | none => rcases hph with rfl | ⟨tk, rfl⟩ <;> simp [putB, putO, hg]
      | some m => cases hnc
  | some g =>
      rw [hg] at hnc
      cases nc with
      | none => cases hnc
      | some m => rcases hph with rfl | ⟨tk, rfl⟩ <;> simp [putB, putO, hg]

end Unfold

section UnfoldV
variable (t : Tag) (cms : List (Dig lam)) (x : Option X) (salt : Bits) (rtreq : Dig lam)
  {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A)
  (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (pl : r.Plain) (pls : Plains s)

/-- the root of a component is taken from the list if and only if the component has a tree -/
theorem takeRt_toList {has : Bool} {rt : Option (Dig lam)}
    (h : rt.isSome = has) (rts : List (Dig lam)) :
    takeRt has (rt.toList ++ rts) = some (rt, rts) := by
  subst h
  cases rt <;> rfl

/-- If the list begins with the roots rt of a component with n trees (there are n of them) and n is
at most `maxRt`, then `takeRts` takes exactly rt and leaves the rest of the list. -/
theorem takeRts_append {n : ℕ} {rt : List (Dig lam)} (h : rt.length = n) (hn : n ≤ maxRt)
    (rts : List (Dig lam)) : takeRts n (rt ++ rts) = some (rt, rts) := by
  have hl : n ≤ (rt ++ rts).length := by
    rw [List.length_append, h]
    exact Nat.le_add_right _ _
  rw [takeRts, if_pos ⟨hn, hl⟩, List.take_left' h, List.drop_left' h]

/-- a round with one query that holds the slot's component -/
theorem chainB_own {ph : Phase lam} {h : Head lam X} {next : Bits → Phase lam}
    (hact : actOf cms (x.map L.early) salt a.kind ph = some (.one h true next))
    (rt : Option (Dig lam)) (hrt : rt.isSome = w.hasJ) (rts : List (Dig lam)) :
    recomputeChain (K := K) t cms x salt rtreq (r :: s) (a, A) (w, W) embP i ph
          (rt.toList ++ rts) (pl, pls) =
        (askTypedOracle (L := L) (K := K) (OracleName.fb t)
          (⟨i, h.withLate (lateInstancePart L i x), rt, embP (.inl (.inr (a.plain pl).2))⟩ : FbIn lam L t)) >>=
      fun ans =>
          (recomputeChain t cms x salt rtreq s A W (fun z => embP (.inr z)) (i + 1)
                (next (List.ofFn ans.2)) rts pls) >>= fun o =>
          pure (o.map fun z => ((w.chal ans.1, z.1), ((none, some rt), z.2.1), z.2.2)) := by
  conv_lhs => unfold recomputeChain
  simp only [hact, takeRt_toList hrt]
  rfl

/-- a round with one query that holds the shared component -/
theorem chainB_shared {ph : Phase lam} {h : Head lam X} {next : Bits → Phase lam}
    (hact : actOf cms (x.map L.early) salt a.kind ph = some (.one h false next))
    (rt : Option (Dig lam)) (hrt : rt.isSome = w.has0) (rts : List (Dig lam)) :
    recomputeChain (K := K) t cms x salt rtreq (r :: s) (a, A) (w, W) embP i ph (rt.toList ++ rts) (pl, pls)
      = (askTypedOracle (L := L) (K := K) (OracleName.fb t) (⟨i, h, rt, embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam L t)) >>= fun ans =>
          (recomputeChain t cms x salt rtreq s A W (fun z => embP (.inr z)) (i + 1)
                (next (List.ofFn ans.2)) rts pls) >>= fun o =>
          pure (o.map fun z => ((w.chal ans.1, z.1), ((some rt, none), z.2.1), z.2.2)) := by
  conv_lhs => unfold recomputeChain
  simp only [hact, takeRt_toList hrt]
  rfl

/-- the joining round -/
theorem chainB_join {ph : Phase lam} {ρ : Bits}
    (hact : actOf cms (x.map L.early) salt a.kind ph = some (.join ρ)) (rtj rt0 : Option (Dig lam))
    (hrtj : rtj.isSome = w.hasJ) (hrt0 : rt0.isSome = w.has0) (rts : List (Dig lam)) :
    recomputeChain (K := K) t cms x salt rtreq (r :: s) (a, A) (w, W) embP i ph
      (rtj.toList ++ (rt0.toList ++ rts)) (pl, pls)
      = (askTypedOracle (L := L) (K := K) (OracleName.g t) (⟨i, ρ, rtj, embP (.inl (.inr (a.plain pl).2))⟩ : JoiningRoundQuery lam L t)) >>= fun c =>
          (askTypedOracle (L := L) (K := K) (OracleName.fb t)
                (⟨i, .f4 cms (List.ofFn rtreq), rt0,
                  embP (.inl (.inl (a.plain pl).1))⟩ : FbIn lam L t)) >>= fun ans =>
          (recomputeChain t cms x salt rtreq s A W (fun z => embP (.inr z)) (i + 1)
                (.shr (List.ofFn ans.2) c) rts pls) >>= fun o =>
          pure (o.map fun z => ((w.chal ans.1, z.1), ((some rt0, some rtj), z.2.1), z.2.2)) := by
  conv_lhs => unfold recomputeChain
  simp only [hact, takeRt_toList hrtj, takeRt_toList hrt0]
  rfl

end UnfoldV

/-! ## Part 2. One slot in one round; all slots -/

section OTree

/-- the tree over a component that may have none: there is a tree if and only if the flag says so,
and then the prover keeps it correctly -/
def OTreeOK (sMT : ℕ) (vs : List Bits) (has : Bool) (tr : Option TTree)
    (d : ℕ) (leaf : ℕ → Body L) : Prop :=
  match has, tr with
  | true, some tr => TTreeOK f sMT vs tr d leaf
  | false, none => True
  | _, _ => False

/-- the root of such a tree, as a digest -/
def rootV (lam : ℕ) (vs : List Bits) (tr : Option TTree) : Option (Dig lam) :=
  tr.map fun tr => dv lam vs tr.root

variable {f}

theorem OTreeOK.mono {sMT : ℕ} {vs vs' : List Bits} (hp : vs <+: vs') :
    ∀ {has : Bool} {tr : Option TTree} {d : ℕ} {leaf : ℕ → Body L},
      OTreeOK f sMT vs has tr d leaf → OTreeOK f sMT vs' has tr d leaf
  | true, some _, _, _, h => TTreeOK.mono hp h
  | false, none, _, _, _ => trivial
  | true, none, _, _, h => h.elim
  | false, some _, _, _, h => h.elim

theorem OTreeOK.rootV_of_prefix {sMT : ℕ} {vs vs' : List Bits} (hp : vs <+: vs') :
    ∀ {has : Bool} {tr : Option TTree} {d : ℕ} {leaf : ℕ → Body L},
      OTreeOK f sMT vs has tr d leaf → rootV lam vs' tr = rootV lam vs tr
  | true, some _, _, _, h => congrArg some (dv_of_prefix hp (TTreeOK.isDig_root h).1)
  | false, none, _, _, _ => rfl
  | true, none, _, _, h => h.elim
  | false, some _, _, _, h => h.elim

theorem OTreeOK.isSome {sMT : ℕ} {vs : List Bits} (vs' : List Bits) :
    ∀ {has : Bool} {tr : Option TTree} {d : ℕ} {leaf : ℕ → Body L},
      OTreeOK f sMT vs has tr d leaf → (rootV lam vs' tr).isSome = has
  | true, some _, _, _, _ => rfl
  | false, none, _, _, _ => rfl
  | true, none, _, _, h => h.elim
  | false, some _, _, _, h => h.elim

variable (f)

/-- the tree over a component, if it has one, and then k -/
theorem tri_withTree {β : Type} (sMT : ℕ) (has : Bool) (d : ℕ) (leaf : ℕ → Body L)
    (k : Option TTree → St lam K L β) (vs : List Bits) (Q : β → List Bits → Prop)
    (h : ∀ tr vs1, vs <+: vs1 → OTreeOK f sMT vs1 has tr d leaf → Tri f (k tr) vs1 Q) :
    Tri f (withTree sMT has d leaf k) vs Q := by
  cases has with
  | true =>
    exact Tri.bind (tri_commitT f sMT d leaf vs).with_prefix fun tr vs1 htr =>
      h (some tr) vs1 htr.2 htr.1
  | false => exact h none vs (List.prefix_refl _) trivial

/-- The trees over a component with a list of trees: there are as many trees as depths, and the
prover keeps tree number n correctly at depth number n and the leaves `leaf n` (`OTreesOK.get`). The
form of `OTreeOK` for a list of trees (`oTreesOK_ite`). -/
def OTreesOK (sMT : ℕ) (vs : List Bits) : List ℕ → List TTree → (ℕ → ℕ → Body L) → Prop
  | [], [], _ => True
  | d :: ds, tr :: trs, leaf =>
    TTreeOK f sMT vs tr d (leaf 0) ∧ OTreesOK sMT vs ds trs fun n => leaf (n + 1)
  | _, _, _ => False

/-- the roots of such trees, as digests -/
def rootsV (lam : ℕ) (vs : List Bits) (trs : List TTree) : List (Dig lam) :=
  trs.map fun tr => dv lam vs tr.root

theorem length_rootsV (vs : List Bits) (trs : List TTree) :
    (rootsV lam vs trs).length = trs.length := by
  simp [rootsV]

variable {f} in
theorem OTreesOK.mono {sMT : ℕ} {vs vs' : List Bits} (hp : vs <+: vs') :
    ∀ {ds : List ℕ} {trs : List TTree} {leaf : ℕ → ℕ → Body L},
      OTreesOK f sMT vs ds trs leaf → OTreesOK f sMT vs' ds trs leaf
  | [], [], _, _ => trivial
  | _ :: _, _ :: _, _, h => ⟨TTreeOK.mono hp h.1, OTreesOK.mono hp h.2⟩
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

variable {f} in
theorem OTreesOK.rootsV_of_prefix {sMT : ℕ} {vs vs' : List Bits} (hp : vs <+: vs') :
    ∀ {ds : List ℕ} {trs : List TTree} {leaf : ℕ → ℕ → Body L},
      OTreesOK f sMT vs ds trs leaf → rootsV lam vs' trs = rootsV lam vs trs
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, _, h =>
    congrArg₂ List.cons (dv_of_prefix hp (TTreeOK.isDig_root h.1).1)
      (OTreesOK.rootsV_of_prefix hp h.2)
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

variable {f} in
/-- as many trees as depths -/
theorem OTreesOK.length_eq {sMT : ℕ} {vs : List Bits} :
    ∀ {ds : List ℕ} {trs : List TTree} {leaf : ℕ → ℕ → Body L},
      OTreesOK f sMT vs ds trs leaf → trs.length = ds.length
  | [], [], _, _ => rfl
  | _ :: _, _ :: _, _, h => congrArg (· + 1) (OTreesOK.length_eq h.2)
  | [], _ :: _, _, h => h.elim
  | _ :: _, [], _, h => h.elim

variable {f} in
/-- tree number n is kept correctly at depth number n and the leaves `leaf n` -/
theorem OTreesOK.get {sMT : ℕ} {vs : List Bits} :
    ∀ {ds : List ℕ} {trs : List TTree} {leaf : ℕ → ℕ → Body L},
      OTreesOK f sMT vs ds trs leaf → ∀ n d, ds[n]? = some d →
        ∃ tr, trs[n]? = some tr ∧ TTreeOK f sMT vs tr d (leaf n)
  | [], [], _, _, _, _, hd => by cases hd
  | _ :: _, tr :: _, _, h, 0, _, hd => by
      cases Option.some.inj hd
      exact ⟨tr, rfl, h.1⟩
  | _ :: _, _ :: _, _, h, n + 1, d, hd => OTreesOK.get h.2 n d hd
  | [], _ :: _, _, h, _, _, _ => h.elim
  | _ :: _, [], _, h, _, _, _ => h.elim

variable {f} in
/-- no root: no depth -/
theorem OTreesOK.nil_of_rootsV {sMT : ℕ} {vs vs' : List Bits} {ds : List ℕ} {trs : List TTree}
    {leaf : ℕ → ℕ → Body L} (h : OTreesOK f sMT vs ds trs leaf) (h0 : rootsV lam vs' trs = []) :
    ds = [] := by
  have h1 := h.length_eq
  have h2 := length_rootsV (lam := lam) vs' trs
  rw [h0] at h2
  exact List.length_eq_zero_iff.1 (by rw [← h1, ← h2]; rfl)

variable {f} in
theorem oTreesOK_ite {sMT : ℕ} {vs : List Bits} (has : Bool) (tr : Option TTree) (d : ℕ)
    (leaf : ℕ → ℕ → Body L) :
    OTreesOK f sMT vs (if has then [d] else []) tr.toList leaf ↔
      OTreeOK f sMT vs has tr d (leaf 0) := by
  cases has <;> cases tr <;> simp [OTreesOK, OTreeOK]

theorem rootsV_toList (vs : List Bits) (tr : Option TTree) :
    rootsV lam vs tr.toList = (rootV lam vs tr).toList := by
  cases tr <;> rfl

/-- the form of `rt_eq_rootV` for a list of trees -/
theorem rt_eq_rootsV (us : List Tok) (trs : List TTree) (vs : List Bits) :
    ((((us ++ trs.map TTree.root).map fun u => vs.getD u []).drop us.length).take
        (trs.map TTree.root).length).map (digD lam) = rootsV lam vs trs := by
  have h : ((us ++ trs.map TTree.root).map fun u => vs.getD u []).drop us.length =
      (trs.map TTree.root).map fun u => vs.getD u [] := by
    rw [List.map_append]
    exact List.drop_left' (by simp)
  rw [h, List.take_of_length_le (by simp)]
  simp [rootsV, dv, List.map_map, Function.comp_def]

/-- the trees over a component with a list of trees, and then k -/
theorem tri_withTrees {β : Type} (sMT : ℕ) :
    ∀ (ds : List ℕ) (leaf : ℕ → ℕ → Body L) (k : List TTree → St lam K L β) (vs : List Bits)
      (Q : β → List Bits → Prop),
      (∀ trs vs1, vs <+: vs1 → OTreesOK f sMT vs1 ds trs leaf → Tri f (k trs) vs1 Q) →
      Tri f (withTrees sMT ds leaf k) vs Q
  | [], _, _, vs, _, h => h [] vs (List.prefix_refl _) trivial
  | d :: ds, leaf, k, vs, Q, h =>
    Tri.bind (tri_commitT f sMT d (leaf 0) vs).with_prefix fun tr vs1 htr =>
      tri_withTrees sMT ds (fun n => leaf (n + 1)) (fun trs => k (tr :: trs)) vs1 Q
        fun trs vs2 hp h2 => h (tr :: trs) vs2 (htr.2.trans hp) ⟨htr.1.mono hp, h2⟩

/-- the root field of a query, as the prover's program writes it -/
theorem rt_eq_rootV (us : List Tok) (tr : Option TTree) (vs : List Bits) :
    ((tr.map TTree.root).map fun _ =>
        digD lam
          (((us ++ (tr.map TTree.root).toList).map fun u => vs.getD u []).getD us.length [])) =
      rootV lam vs tr := by
  cases tr with
  | none => rfl
  | some tr =>
    show some (digD lam (((us ++ [tr.root]).map fun u => vs.getD u []).getD us.length [])) =
      some (digD lam (vs.getD tr.root []))
    simp

end OTree

section Slot
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X)

/-- what the tokens of a slot must be, relative to a store, for the phase ph -/
def SlotPre (vs : List Bits) : PhT → SlotAcc lam K Y → Prop
  | .first, acc => acc.tk < vs.length
  | .loc, acc => acc.tk < vs.length
  | .shr tk0, acc => tk0 < vs.length ∧ IsDig lam vs acc.c
  | .aft, acc => acc.tk < vs.length ∧ IsDig lam vs acc.c

theorem SlotPre.mono {vs vs' : List Bits} (hp : vs <+: vs') :
    ∀ {ph : PhT} {acc : SlotAcc lam K Y}, SlotPre vs ph acc → SlotPre vs' ph acc
  | .first, _, h => lt_of_lt_of_le h hp.length_le
  | .loc, _, h => lt_of_lt_of_le h hp.length_le
  | .shr _, _, h => ⟨lt_of_lt_of_le h.1 hp.length_le, h.2.mono hp⟩
  | .aft, _, h => ⟨lt_of_lt_of_le h.1 hp.length_le, h.2.mono hp⟩

/-- the phase of the verifier's chain that corresponds to the prover's phase and the tokens of the
slot -/
def phV (vs : List Bits) : PhT → SlotAcc lam K Y → Phase lam
  | .first, _ => .first
  | .loc, acc => .loc (vs.getD acc.tk [])
  | .shr tk0, acc => .shr (vs.getD tk0 []) (dv lam vs acc.c)
  | .aft, acc => .aft (vs.getD acc.tk []) (dv lam vs acc.c)

theorem phV_of_prefix {vs vs' : List Bits} (hp : vs <+: vs') :
    ∀ {ph : PhT} {acc : SlotAcc lam K Y}, SlotPre vs ph acc → phV vs' ph acc = phV vs ph acc
  | .first, _, _ => rfl
  | .loc, _, h => by simp only [phV, getD_of_prefix hp h]
  | .shr _, _, h => by simp only [phV, getD_of_prefix hp h.1, dv_of_prefix hp h.2.1]
  | .aft, _, h => by simp only [phV, getD_of_prefix hp h.1, dv_of_prefix hp h.2.1]

/-- the header of the Fiat-Shamir query of a slot in the local round i; x is the whole instance of
the slot: (F1) holds L.early x, and (F2) holds x in the round L.late -/
def headLo (L : BatchProtocol I X) (vs : List Bits) (x : Option X) (i : ℕ) :
    PhT → SlotAcc lam K Y → Head lam X
  | .first, acc => .f1 cms (x.map L.early) (vs.getD acc.tk [])
  | .loc, acc => .f2 (lateInstancePart L i x) (vs.getD acc.tk [])
  | .shr tk0, acc => .f3 (vs.getD tk0 []) (vs.getD acc.c [])
  | .aft, acc => .f2 (lateInstancePart L i x) (vs.getD acc.tk [])

/-- the verifier first forms the header without the late field and then writes the field -/
theorem headLo_late (vs : List Bits) (x : Option X) (i : ℕ) : ∀ (ph : PhT) (acc : SlotAcc lam K Y),
    ((headLo cms L vs x i ph acc).withLate none).withLate (lateInstancePart L i x) = headLo cms L vs x i ph acc
  | .first, _ => rfl
  | .loc, _ => rfl
  | .shr _, _ => rfl
  | .aft, _ => rfl

/-- the verifier's phase after a local round -/
def nextLo (vs : List Bits) : PhT → SlotAcc lam K Y → Bits → Phase lam
  | .first, _ => .loc
  | .loc, _ => .loc
  | .shr _, acc => fun v => .aft v (dv lam vs acc.c)
  | .aft, acc => fun v => .aft v (dv lam vs acc.c)

/-- Under `SlotPre`, with the prover's salt: in a local round the verifier makes the query of the
prover. -/
theorem actOf_lo (vs : List Bits) (x : Option X) (i : ℕ) (salt : Bits) :
    ∀ (ph : PhT) (acc : SlotAcc lam K Y), SlotPre vs ph acc →
      (ph = .first → salt = vs.getD acc.tk []) →
      actOf cms (x.map L.early) salt .lo (phV vs ph acc) =
        some (.one ((headLo cms L vs x i ph acc).withLate none) true (nextLo vs ph acc))
  | .first, _, _, hs => by rw [hs rfl]; rfl
  | .loc, _, _, _ => rfl
  | .shr _, _, h, _ => by simp only [phV, actOf, headLo, nextLo, Head.withLate, ← h.2.2]
  | .aft, _, _, _ => rfl

theorem headLo_of_prefix {vs vs' : List Bits} (hp : vs <+: vs') (x : Option X) (i : ℕ) :
    ∀ {ph : PhT} {acc : SlotAcc lam K Y},
      SlotPre vs ph acc → headLo cms L vs' x i ph acc = headLo cms L vs x i ph acc
  | .first, _, h => by simp only [headLo, getD_of_prefix hp h]
  | .loc, _, h => by simp only [headLo, getD_of_prefix hp h]
  | .shr _, _, h => by simp only [headLo, getD_of_prefix hp h.1, getD_of_prefix hp h.2.1]
  | .aft, _, h => by simp only [headLo, getD_of_prefix hp h.1]

/-- under `SlotPre` at vs, for a store vs' that begins with vs (hp): after a local round, the
verifier's phase is the one that corresponds to the new tail -/
theorem phV_afterLo {vs vs' : List Bits} (hp : vs <+: vs') (tl : Tok) :
    ∀ {ph : PhT} {acc : SlotAcc lam K Y}, SlotPre vs ph acc →
      ∀ (bl : List (Blk lam K)) (tr : List (Option TTree)) (tk : List Tok)
          (nn : List ℕ) (dd : List Tok),
        phV vs' ph.afterLo (⟨acc.x, tl, acc.c, bl, tr, tk, nn, dd⟩ : SlotAcc lam K Y) =
          nextLo vs ph acc (vs'.getD tl [])
  | .first, _, _, _, _, _, _, _ => rfl
  | .loc, _, _, _, _, _, _, _ => rfl
  | .shr _, _, h, _, _, _, _, _ => by simp only [PhT.afterLo, phV, nextLo, dv_of_prefix hp h.2.1]
  | .aft, _, h, _, _, _, _, _ => by simp only [PhT.afterLo, phV, nextLo, dv_of_prefix hp h.2.1]

theorem slotPre_afterLo {vs vs' : List Bits} (hp : vs <+: vs') {tl : Tok} (htl : tl < vs'.length) :
    ∀ {ph : PhT} {acc : SlotAcc lam K Y}, SlotPre vs ph acc →
      ∀ (bl : List (Blk lam K)) (tr : List (Option TTree)) (tk : List Tok)
          (nn : List ℕ) (dd : List Tok),
        SlotPre vs' ph.afterLo (⟨acc.x, tl, acc.c, bl, tr, tk, nn, dd⟩ : SlotAcc lam K Y)
  | .first, _, _, _, _, _, _, _ => htl
  | .loc, _, _, _, _, _, _, _ => htl
  | .shr _, _, h, _, _, _, _, _ => ⟨htl, h.2.mono hp⟩
  | .aft, _, h, _, _, _, _, _ => ⟨htl, h.2.mono hp⟩

variable {r : Round} {s : Shape} (a : RAnn r) (w : WireRB lam K r a)
  (emb : (p : r.Pos) → r.Sym p → Body L) (plJ : a.Pj → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)

omit a w emb plJ in
/-- a Fiat-Shamir query, for fixed oracle functions -/
theorem tri_fbT {β : Type} (tk : Tok) (us : List Tok) (tr : Option TTree)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) (k : Blk lam K → Tok → St lam K L β)
    (vs : List Bits) (Q : β → List Bits → Prop) :
    Tri f (fbT t i tk us (tr.map TTree.root) hd hinj pl k) vs Q ↔
    Tri f (k (f (OracleName.fb t)
          (⟨i, hd ((us ++ (tr.map TTree.root).toList).map fun u => vs.getD u []) (vs.getD tk []),
            rootV lam vs tr,
            pl⟩ : FbIn lam L t)).1 vs.length)
      (vs ++ [List.ofFn
            (f (OracleName.fb t)
              (⟨i, hd ((us ++ (tr.map TTree.root).toList).map fun u => vs.getD u [])
                  (vs.getD tk []),
                rootV lam vs tr,
                pl⟩ : FbIn lam L t)).2]) Q := by
  rw [← rt_eq_rootV us tr vs]
  exact Iff.rfl

omit a w emb plJ in
/-- the same at a ghost name fbw t j -/
theorem tri_fbTw {β : Type} (j : ℕ) (tk : Tok) (us : List Tok) (tr : Option TTree)
    (hd : List Bits → Bits → Head lam X) (hinj : ∀ vs, Function.Injective (hd vs))
    (pl : PlainPart (shapeOf L t) (annOf L t)) (k : Blk lam K → Tok → St lam K L β)
    (vs : List Bits) (Q : β → List Bits → Prop) :
    Tri f (fbTw t j i tk us (tr.map TTree.root) hd hinj pl k) vs Q ↔
    Tri f (k (f (OracleName.fbw t j)
          (⟨i, hd ((us ++ (tr.map TTree.root).toList).map fun u => vs.getD u []) (vs.getD tk []),
            rootV lam vs tr,
            pl⟩ : FbIn lam L t)).1 vs.length)
      (vs ++ [List.ofFn
            (f (OracleName.fbw t j)
              (⟨i, hd ((us ++ (tr.map TTree.root).toList).map fun u => vs.getD u [])
                  (vs.getD tk []),
                rootV lam vs tr,
                pl⟩ : FbIn lam L t)).2]) Q := by
  rw [← rt_eq_rootV us tr vs]
  exact Iff.rfl

omit a w emb plJ in
/-- the attempts after the first -/
theorem tri_fbW (hf : RealFam f) {β C P : Type} (g : GrW C P) (chal : Blk lam K → C) (tk : Tok)
    (us : List Tok) (tr : Option TTree) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    (k : ℕ → List Tok → Blk lam K → Tok → St lam K L β) (vs : List Bits) (Q : β → List Bits → Prop)
    (h0 : Head lam X) (rt : Option (Dig lam))
    (hst : ∀ vs1, vs <+: vs1 →
      hd ((us ++ (tr.map TTree.root).toList).map fun u => vs1.getD u []) (vs1.getD tk []) = h0 ∧
      rootV lam vs1 tr = rt)
    (h : ∀ (m : ℕ) (dd : List Tok) (vs1 : List Bits), vs <+: vs1 →
      Tri f (k m dd (f (OracleName.fb t) (⟨i, h0, rt, emb (g.put m α)⟩ : FbIn lam L t)).1 vs1.length)
        (vs1 ++ [List.ofFn (f (OracleName.fb t) (⟨i, h0, rt, emb (g.put m α)⟩ : FbIn lam L t)).2]) Q) :
    ∀ (n j : ℕ) (dd : List Tok) (vs1 : List Bits),
      vs <+: vs1 → Tri f (fbW g chal t i tk us (tr.map TTree.root) hd hinj emb α k n j dd) vs1 Q
  | 0, j, dd, vs1, hp => by
      rw [fbW, tri_fbTw, (hst vs1 hp).1, (hst vs1 hp).2, hf]
      exact h (j + 1) dd vs1 hp
  | n + 1, j, dd, vs1, hp => by
      rw [fbW, tri_fbTw, (hst vs1 hp).1, (hst vs1 hp).2, hf]
      by_cases hok : g.ok
          (chal (f (OracleName.fb t) (⟨i, h0, rt, emb (g.put (j + 1) α)⟩ : FbIn lam L t)).1) = true
      · rw [if_pos hok]
        exact h (j + 1) dd vs1 hp
      · rw [if_neg hok]
        exact tri_fbW hf g chal tk us tr hd hinj emb α k vs Q h0 rt hst h n (j + 1)
          _ _ (hp.trans (List.prefix_append _ _))

omit a w emb plJ in
/-- A Fiat-Shamir query with proof-of-work bits or without, for fixed oracle functions with
`RealFam`. Whatever the search does: what follows is run on the answer of `fb t` at the query whose
plain part holds the number of the final attempt, in a store that has grown. h0, rt: the header and
the root of the query, which do not change while the store grows. -/
theorem tri_fbG (hf : RealFam f) {β C P : Type} (gr : Option (GrW C P)) (chal : Blk lam K → C)
    (tk : Tok) (us : List Tok) (tr : Option TTree) (hd : List Bits → Bits → Head lam X)
    (hinj : ∀ vs, Function.Injective (hd vs)) (emb : P → PlainPart (shapeOf L t) (annOf L t)) (α : P)
    (k : Option ℕ → List Tok → Blk lam K → Tok → St lam K L β) (vs : List Bits)
    (Q : β → List Bits → Prop) (h0 : Head lam X) (rt : Option (Dig lam))
    (hst : ∀ vs1, vs <+: vs1 →
      hd ((us ++ (tr.map TTree.root).toList).map fun u => vs1.getD u []) (vs1.getD tk []) = h0 ∧
      rootV lam vs1 tr = rt)
    (h : ∀ (nc : Option ℕ) (dd : List Tok) (vs1 : List Bits), vs <+: vs1 → nc.isSome = gr.isSome →
      Tri f (k nc dd (f (OracleName.fb t) (⟨i, h0, rt, emb (putO gr nc α)⟩ : FbIn lam L t)).1 vs1.length)
        (vs1 ++ [List.ofFn (f (OracleName.fb t) (⟨i, h0, rt, emb (putO gr nc α)⟩ : FbIn lam L t)).2]) Q) :
    Tri f (fbG gr chal t i tk us (tr.map TTree.root) hd hinj emb α k) vs Q := by
  have e := hst vs (List.prefix_refl _)
  cases gr with
  | none =>
      rw [fbG_none, tri_fbT, e.1, e.2]
      exact h none [] vs (List.prefix_refl _) rfl
  | some g =>
      show Tri f (fbTG g chal t i tk us (tr.map TTree.root) hd hinj emb α fun m => k (some m)) vs Q
      unfold fbTG
      split
      · rw [tri_fbT, e.1, e.2]
        exact h (some 0) [] vs (List.prefix_refl _) rfl
      · rw [tri_fbT, e.1, e.2]
        by_cases hok : g.ok (chal (f (OracleName.fb t) (⟨i, h0, rt, emb (g.put 0 α)⟩ : FbIn lam L t)).1) =
          true
        · rw [if_pos hok]
          exact h (some 0) [] vs (List.prefix_refl _) rfl
        · rw [if_neg hok]
          exact tri_fbW f t i hf g chal tk us tr hd hinj emb α (fun m => k (some m)) vs Q h0 rt hst
            (fun m dd vs1 hp => h (some m) dd vs1 hp rfl) _ 0 _ _ (List.prefix_append _ _)

/-- A local round in one slot, under `RealFam`, `SlotPre`. q is the query of the final attempt in
the slot's chain; nc its number, if the round has proof-of-work bits; dd a list of tokens (in the
program: the tails of the failed attempts). -/
theorem tri_slotLo (hf : RealFam f) (ph : PhT) (m : r.Msg) (k : r.Chal → Strat s Unit)
    (acc : SlotAcc lam K Y) (vs : List Bits) (hpre : SlotPre vs ph acc) :
    Tri f (slotLo sMT t cms xin a w emb plJ i ph ((m, k), acc)) vs fun z' vs' =>
      ∃ (tr : Option TTree) (tl : Tok) (q : FbIn lam L t) (nc : Option ℕ) (dd : List Tok),
          nc.isSome = w.grJ.isSome ∧
          q = ⟨i, headLo cms L vs (acc.x.bind xin) i ph acc,
              rootV lam vs' tr, plJ (putO w.grJ nc (a.plain m.2).2)⟩ ∧
          OTreeOK f sMT vs' w.hasJ tr w.depthJ (bodyAt w.posAtJ emb m.1) ∧
          tl < vs'.length ∧
          vs'.getD tl [] = List.ofFn (f (OracleName.fb t) q).2 ∧
          z' = (k (w.chal (f (OracleName.fb t) q).1),
              ⟨acc.x, tl, acc.c, acc.blocks ++ [(f (OracleName.fb t) q).1], acc.trees ++ [tr],
                acc.toks ++ [tl], nc.toList ++ acc.nons, dd ++ acc.dead⟩) := by
  unfold slotLo
  refine tri_withTree f sMT w.hasJ w.depthJ (bodyAt w.posAtJ emb m.1) _ vs _ fun tr vs1 hp htr => ?_
  cases ph with
  | first =>
    simp only [fbSlotG]
    exact tri_fbG f t i hf w.grJ w.chal _ _ tr _ _ plJ _ _ vs1 _
      (headLo cms L vs (acc.x.bind xin) i .first acc) (rootV lam vs1 tr)
      (fun vs2 hp2 =>
        ⟨by simp only [headLo, getD_of_prefix (hp.trans hp2) (show acc.tk < vs.length from hpre)],
          htr.rootV_of_prefix hp2⟩)
      (fun nc dd vs2 hp2 hnc =>
        tri_pure_iff.2
          ⟨tr, vs2.length, _, nc, dd, hnc,
            by rw [htr.rootV_of_prefix (hp2.trans (List.prefix_append _ _))],
            htr.mono (hp2.trans (List.prefix_append _ _)), by simp, getD_concat_length _ _, rfl⟩)
  | loc =>
    simp only [fbSlotG]
    exact tri_fbG f t i hf w.grJ w.chal _ _ tr _ _ plJ _ _ vs1 _
      (headLo cms L vs (acc.x.bind xin) i .loc acc) (rootV lam vs1 tr)
      (fun vs2 hp2 =>
        ⟨by simp only [headLo, getD_of_prefix (hp.trans hp2) (show acc.tk < vs.length from hpre)],
          htr.rootV_of_prefix hp2⟩)
      (fun nc dd vs2 hp2 hnc =>
        tri_pure_iff.2
          ⟨tr, vs2.length, _, nc, dd, hnc,
            by rw [htr.rootV_of_prefix (hp2.trans (List.prefix_append _ _))],
            htr.mono (hp2.trans (List.prefix_append _ _)), by simp, getD_concat_length _ _, rfl⟩)
  | shr tk0 =>
    simp only [fbSlotG]
    exact tri_fbG f t i hf w.grJ w.chal _ _ tr _ _ plJ _ _ vs1 _ (headLo cms L vs (acc.x.bind xin) i (.shr tk0) acc) (rootV lam vs1 tr) (fun vs2 hp2 => ⟨by
      simp only [headLo, ← getD_of_prefix (hp.trans hp2) hpre.1,
        ← getD_of_prefix (hp.trans hp2) hpre.2.1]
      rfl, htr.rootV_of_prefix hp2⟩) (fun nc dd vs2 hp2 hnc => tri_pure_iff.2 ⟨tr, vs2.length, _, nc, dd, hnc, by rw [htr.rootV_of_prefix (hp2.trans (List.prefix_append _ _))],
      htr.mono (hp2.trans (List.prefix_append _ _)), by simp, getD_concat_length _ _, rfl⟩)
  | aft =>
    simp only [fbSlotG]
    exact tri_fbG f t i hf w.grJ w.chal _ _ tr _ _ plJ _ _ vs1 _
      (headLo cms L vs (acc.x.bind xin) i .aft acc) (rootV lam vs1 tr)
      (fun vs2 hp2 =>
        ⟨by simp only [headLo, getD_of_prefix (hp.trans hp2) hpre.1], htr.rootV_of_prefix hp2⟩)
      (fun nc dd vs2 hp2 hnc =>
        tri_pure_iff.2
          ⟨tr, vs2.length, _, nc, dd, hnc,
            by rw [htr.rootV_of_prefix (hp2.trans (List.prefix_append _ _))],
            htr.mono (hp2.trans (List.prefix_append _ _)), by simp, getD_concat_length _ _, rfl⟩)

/-- The joining round in one slot, under acc.tk < vs.length (hpre). q is the query to g; its answer
is the slot value. -/
theorem tri_slotJoin (m : r.Msg) (k : r.Chal → Strat s Unit) (acc : SlotAcc lam K Y)
    (vs : List Bits) (hpre : acc.tk < vs.length) :
    Tri f (slotJoin sMT t a w emb plJ i ((m, k), acc)) vs fun z' vs' =>
      ∃ (tr : Option TTree) (c : Tok) (q : JoiningRoundQuery lam L t),
          q = ⟨i, vs.getD acc.tk [], rootV lam vs' tr, plJ (a.plain m.2).2⟩ ∧
          OTreeOK f sMT vs' w.hasJ tr w.depthJ (bodyAt w.posAtJ emb m.1) ∧
          IsDig lam vs' c ∧
          dv lam vs' c = f (OracleName.g t) q ∧
          z' = ((m, k),
              ⟨acc.x, acc.tk, c, acc.blocks, acc.trees ++ [tr], acc.toks ++ [c],
                acc.nons, acc.dead⟩) := by
  unfold slotJoin
  refine tri_withTree f sMT w.hasJ w.depthJ (bodyAt w.posAtJ emb m.1) _ vs _ fun tr vs1 hp htr => ?_
  have hroot : ∀ x : Bits, rootV lam (vs1 ++ [x]) tr = rootV lam vs1 tr := fun x =>
    htr.rootV_of_prefix (List.prefix_append _ _)
  have hrt : ((tr.map TTree.root).map fun _ =>
        digD lam (((tr.map TTree.root).toList.map fun u => vs1.getD u []).headD [])) =
      rootV lam vs1 tr := by
    cases tr <;> rfl
  unfold gT
  refine tri_marked_iff.2 (tri_pure_iff.2 ?_)
  have hd := isDig_concat vs1
    (f (OracleName.g t)
      (⟨i, vs1.getD acc.tk [],
        (tr.map TTree.root).map fun _ =>
          digD lam (((tr.map TTree.root).toList.map fun u => vs1.getD u []).headD []),
        plJ (a.plain m.2).2⟩ : JoiningRoundQuery lam L t))
  refine ⟨tr, vs1.length, _, ?_, htr.mono (List.prefix_append _ _), hd.1, hd.2, rfl⟩
  rw [hroot, getD_of_prefix hp hpre, hrt]

end Slot

/-! ### All slots -/

section All
variable {f}

theorem forall₂_comp {α β γ : Type} {P : α → β → Prop} {Q : β → γ → Prop}
    {R : α → γ → Prop} (h : ∀ a b c, P a b → Q b c → R a c) :
    ∀ {l₁ : List α} {l₂ : List β} {l₃ : List γ},
      List.Forall₂ P l₁ l₂ → List.Forall₂ Q l₂ l₃ → List.Forall₂ R l₁ l₃
  | _, _, _, .nil, .nil => .nil
  | _, _, _, .cons h1 t1, .cons h2 t2 => .cons (h _ _ _ h1 h2) (forall₂_comp h t1 t2)

/-- run g in each slot: what holds of each slot before, and is kept when the store grows, gives what
g ensures (which must be kept too when the store grows: hPost), for all slots, at the end -/
theorem tri_eachM {σ τ : Type} (g : σ → St lam K L τ) (Pre : σ → List Bits → Prop)
    (Post : σ → τ → List Bits → Prop) (hPre : ∀ z vs vs', vs <+: vs' → Pre z vs → Pre z vs')
    (hPost : ∀ z z' vs vs', vs <+: vs' → Post z z' vs → Post z z' vs')
    (hg : ∀ z vs, Pre z vs → Tri f (g z) vs fun z' vs' => Post z z' vs') :
    ∀ (zs : List σ) (vs : List Bits), (∀ z ∈ zs, Pre z vs) →
      Tri f (eachM g zs) vs fun zs' vs' => List.Forall₂ (fun z z' => Post z z' vs') zs zs'
  | [], _, _ => tri_pure_iff.2 .nil
  | z :: zs, vs, h => by
      refine Tri.bind (hg z vs (h z (by simp))).with_prefix fun z' vs1 hz => ?_
      refine Tri.bind
        (tri_eachM g Pre Post hPre hPost hg zs vs1 fun u hu =>
          hPre u vs vs1 hz.2 (h u (by simp [hu]))).with_prefix
        fun r vs2 hr => tri_pure_iff.2 (.cons (hPost z z' vs1 vs2 hr.2 hz.1) hr.1)

end All

/-! ## Part 3. The chain -/

section Chain
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq : ℕ)

def fph : PhT → FPhase
  | .first => .first
  | .loc => .loc
  | .shr _ => .shr
  | .aft => .aft

theorem fph_afterLo (ph : PhT) : fph ph.afterLo = (fph ph).afterLo := by cases ph <;> rfl

/-- one component of one round: it has no tree and no root; or the prover keeps its tree correctly,
and the verifier has its root -/
def CompOK (vs : List Bits) (tr : Option TTree) (rt : Option (Dig lam))
    (d : ℕ) (leaf : ℕ → Body L) : Prop :=
  match tr, rt with
  | none, none => True
  | some tr, some c => TTreeOK f sMT vs tr d leaf ∧ c = dv lam vs tr.root
  | _, _ => False

variable {f sMT} in
theorem CompOK.mono {vs vs' : List Bits} (hp : vs <+: vs') :
    ∀ {tr : Option TTree} {rt : Option (Dig lam)} {d : ℕ} {leaf : ℕ → Body L},
      CompOK f sMT vs tr rt d leaf → CompOK f sMT vs' tr rt d leaf
  | none, none, _, _, _ => trivial
  | some _, some _, _, _, h => ⟨h.1.mono hp, by rw [dv_of_prefix hp h.1.isDig_root.1]; exact h.2⟩
  | none, some _, _, _, h => h.elim
  | some _, none, _, _, h => h.elim

variable {f sMT} in
theorem OTreeOK.compOK {vs : List Bits} :
    ∀ {has : Bool} {tr : Option TTree} {d : ℕ} {leaf : ℕ → Body L},
      OTreeOK f sMT vs has tr d leaf → CompOK f sMT vs tr (rootV lam vs tr) d leaf
  | true, some _, _, _, h => ⟨h, rfl⟩
  | false, none, _, _, _ => trivial
  | true, none, _, _, h => h.elim
  | false, some _, _, _, h => h.elim

/-- One component of one round, with a list of trees: it has no tree and no root; or the prover
keeps its trees correctly, and the verifier has their roots. It does not say why a component has no
tree: that it is not sent, or has no depth. The form of `CompOK` for a list of trees
(`compsOK_one`). -/
def CompsOK (sMT : ℕ) (vs : List Bits) (trs : List TTree) (rts : List (Dig lam)) (ds : List ℕ)
    (leaf : ℕ → ℕ → Body L) : Prop :=
  (trs = [] ∧ rts = []) ∨ (OTreesOK f sMT vs ds trs leaf ∧ rts = rootsV lam vs trs)

variable {f} in
theorem CompsOK.mono {sMT : ℕ} {vs vs' : List Bits} (hp : vs <+: vs') {trs : List TTree}
    {rts : List (Dig lam)} {ds : List ℕ} {leaf : ℕ → ℕ → Body L}
    (h : CompsOK f sMT vs trs rts ds leaf) : CompsOK f sMT vs' trs rts ds leaf := by
  rcases h with h | ⟨h1, h2⟩
  · exact .inl h
  · exact .inr ⟨h1.mono hp, by rw [h1.rootsV_of_prefix hp]; exact h2⟩

variable {f} in
theorem OTreesOK.compsOK {sMT : ℕ} {vs : List Bits} {ds : List ℕ} {trs : List TTree}
    {leaf : ℕ → ℕ → Body L} (h : OTreesOK f sMT vs ds trs leaf) :
    CompsOK f sMT vs trs (rootsV lam vs trs) ds leaf := .inr ⟨h, rfl⟩

variable {f} in
theorem compsOK_one {sMT : ℕ} {vs : List Bits} (tr : Option TTree) (rt : Option (Dig lam)) (d : ℕ)
    (leaf : ℕ → ℕ → Body L) :
    CompsOK f sMT vs tr.toList rt.toList [d] leaf ↔ CompOK f sMT vs tr rt d (leaf 0) := by
  cases tr <;> cases rt <;> simp [CompsOK, CompOK, OTreesOK, rootsV]

variable {f sMT} in
theorem OTreeOK.has_false {vs vs' : List Bits} :
    ∀ {has : Bool} {tr : Option TTree} {d : ℕ} {leaf : ℕ → Body L},
      OTreeOK f sMT vs has tr d leaf → rootV lam vs' tr = none → has = false
  | true, some _, _, _, _, h => by cases h
  | false, none, _, _, _, _ => rfl
  | true, none, _, _, h, _ => h.elim
  | false, some _, _, _, h, _ => h.elim

/-- under `w.OKG`, a slot's component without a tree has no oracle position -/
theorem own_false_of_noJ {r : Round} {a : RAnn r} {w : WireRB lam K r a} (hw : w.OKG)
    (h : w.hasJ = false) (p : r.Pos) : a.own p = false := by
  cases ho : a.own p with
  | false => rfl
  | true =>
    have h1 := hw.posAtJ_place p ho
    rw [hw.noJ h] at h1
    cases h1

/-- under `w.OKG`, a shared component without a tree has no oracle position -/
theorem own_true_of_no0 {r : Round} {a : RAnn r} {w : WireRB lam K r a} (hw : w.OKG)
    (h : w.has0 = false) (p : r.Pos) : a.own p = true := by
  cases ho : a.own p with
  | true => rfl
  | false =>
    have h1 := hw.posAt0_place p ho
    rw [hw.no0 h] at h1
    cases h1

theorem map_rootToks_cons (vs : List Bits) (tj t0 : Option TTree) (tjs t0s : List (Option TTree)) :
    (rootToks (tj :: tjs) (t0 :: t0s)).map (dv lam vs) =
      (rootV lam vs tj).toList ++
        ((rootV lam vs t0).toList ++ (rootToks tjs t0s).map (dv lam vs)) := by
  cases tj <;> cases t0 <;> simp [rootToks, rootV]

/-- The trees of all rounds of a local transcript are kept correctly, relative to a store: tjs are
the trees over the slot's components, t0s those over the shared components, rts the roots as the
verifier has them; a component that is not sent is empty; and a component without a root has no
oracle position. -/
def RoundsOK (vs : List Bits) :
    (s : Shape) → (A : RoundSplits s) → RoundsQueryLayout lam K s A → ((p : OPos s) → OSym s p → Body L) →
    Tr s → List (Option TTree) → List (Option TTree) → RootsOfChain lam s → Prop
  | [], _, _, _, _, tjs, t0s, _ => tjs = [] ∧ t0s = []
  | _ :: s, (a, A), (w, W), embS, (m, _, τ), tjs, t0s, (rt, rts) =>
      ∃ tj t0 tjs' t0s', tjs = tj :: tjs' ∧ t0s = t0 :: t0s' ∧
        CompOK f sMT vs t0 rt.1.join w.depth0 (bodyAt w.posAt0 (fun p => embS (.inl p)) m.1) ∧
        CompOK f sMT vs tj rt.2.join w.depthJ (bodyAt w.posAtJ (fun p => embS (.inl p)) m.1) ∧
        (rt.1 = none → a.NoShared) ∧ (rt.2 = none → a.NoSlot) ∧
        (rt.1.join = none → ∀ p, a.own p = true) ∧ (rt.2.join = none → ∀ p, a.own p = false) ∧
        RoundsOK vs s A W (fun p => embS (.inr p)) τ tjs' t0s' rts

variable {f sMT} in
theorem RoundsOK.mono {vs vs' : List Bits} (hp : vs <+: vs') :
    ∀ {s : Shape} {A : RoundSplits s} {W : RoundsQueryLayout lam K s A} {embS : (p : OPos s) → OSym s p → Body L}
        {τ : Tr s} {tjs t0s : List (Option TTree)} {rts : RootsOfChain lam s},
      RoundsOK f sMT vs s A W embS τ tjs t0s rts → RoundsOK f sMT vs' s A W embS τ tjs t0s rts
  | [], _, _, _, _, _, _, _, h => h
  | _ :: _, (_, _), (_, _), _, (_, _, _), _, _, (_, _), h => by
      obtain ⟨tj, t0, tjs', t0s', h1, h2, h3, h4, h5, h6, h8, h9, h7⟩ := h
      exact ⟨tj, t0, tjs', t0s', h1, h2, h3.mono hp, h4.mono hp, h5, h6, h8,
        h9, RoundsOK.mono hp h7⟩

/-- the chains have joined -/
def chainsHaveJoined : PhT → Prop
  | .first => False
  | .loc => False
  | .shr _ => True
  | .aft => True

/-- the request tree, by the phase: there is none before the chains have joined; afterwards it is
the tree over the slot values of all slots -/
def ReqInv (vs : List Bits) (ph : PhT) (req : Option TTree) (cs : List Tok) : Prop :=
  (¬ chainsHaveJoined ph → req = none) ∧
  (chainsHaveJoined ph →
    ∃ rq, req = some rq ∧ ReqOK f vs rq depthReq (cs.map (dv lam vs)) ∧ cs.length = 2 ^ depthReq)

/-- What the chain ensures for one slot. z is the slot before the rounds s, in the phase ph and with
the store vs0; acc' is what it has gathered after them, in the phase phE and with the store vs'. If
the slot's strategy is the shared strategy σ0 with a strategy of its own, the verifier's chain,
given the roots, the plain parts with the numbers of the final attempts written in (nJ: the slot's,
n0s: the shared ones, in the order of the rounds), the salt and the request root, recomputes the
slot's verifier messages. -/
def SlotDone (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A)
    (embS : (p : OPos s) → OSym s p → Body L) (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)
    (ph phE : PhT) (vs0 : List Bits) (σ0 : SStrat s A) (t0s : List (Option TTree)) (n0s : List ℕ)
    (req' : Option TTree) (vs' : List Bits) (z : SlotSt lam K Y s) (acc' : SlotAcc lam K Y) :
    Prop :=
  acc'.x = z.2.x ∧ (∃ more, acc'.toks = z.2.toks ++ more) ∧
  SlotPre vs' phE acc' ∧ (chainsHaveJoined ph → acc'.c = z.2.c) ∧
  ∃ bls tjs nJ,
    acc'.blocks = z.2.blocks ++ bls ∧
    acc'.trees = z.2.trees ++ tjs ∧
    acc'.nons = nJ.reverse ++ z.2.nons ∧
    ∀ σj, z.1 = σ0.zip σj →
      ∀ (salt : Bits) (rtreq : Dig lam), (ph = .first → salt = vs0.getD z.2.tk []) →
        (∀ rq, req' = some rq → rtreq = dv lam vs' rq.root) →
        ∃ rts,
          RoundsOK f sMT vs' s A W embS (z.1.run (rhoOf s A W bls)).1 tjs t0s rts ∧
          EvalsTo f (recomputeChain t cms (z.2.x.bind xin) salt rtreq s A W embP i (phV vs0 ph z.2)
              ((rootToks tjs t0s).map (dv lam vs'))
              (putB s A W ph nJ n0s (z.1.run (rhoOf s A W bls)).1.plains))
            (some (rhoOf s A W bls, rts, phV vs' phE acc'))

/-- there is no shared round -/
def AllLo : (s : Shape) → RoundSplits s → Prop
  | [], _ => True
  | _ :: s, (a, A) => a.kind = .lo ∧ AllLo s A

end Chain

section Steps
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq : ℕ)
  {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A)
  (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
  (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)

/-- what a local round ensures for one slot; vs is the store at the start of the round -/
def LoPost (ph : PhT) (vs : List Bits) (z : SlotSt lam K Y (r :: s))
    (z' : SlotSt lam K Y s) (vs' : List Bits) : Prop :=
  ∃ (tr : Option TTree) (tl : Tok) (q : FbIn lam L t) (nc : Option ℕ) (dd : List Tok),
    nc.isSome = w.grJ.isSome ∧
    q = ⟨i, headLo cms L vs (z.2.x.bind xin) i ph z.2,
        rootV lam vs' tr,
        embP (.inl (.inr (putO w.grJ nc (a.plain z.1.1.2).2)))⟩ ∧
    OTreeOK f sMT vs' w.hasJ tr w.depthJ (bodyAt w.posAtJ (fun p => embS (.inl p)) z.1.1.1) ∧
    tl < vs'.length ∧
    vs'.getD tl [] = List.ofFn (f (OracleName.fb t) q).2 ∧
    z' = (z.1.2 (w.chal (f (OracleName.fb t) q).1),
        ⟨z.2.x, tl, z.2.c, z.2.blocks ++ [(f (OracleName.fb t) q).1], z.2.trees ++ [tr], z.2.toks ++ [tl],
          nc.toList ++ z.2.nons, dd ++ z.2.dead⟩)

variable {f sMT t cms xin a A w embS embP i} in
theorem LoPost.mono {ph : PhT} {vs : List Bits} {z : SlotSt lam K Y (r :: s)}
    {z' : SlotSt lam K Y s} {vs1 vs2 : List Bits} (hp : vs1 <+: vs2)
    (h : LoPost f sMT t cms xin a A w embS embP i ph vs z z' vs1) :
    LoPost f sMT t cms xin a A w embS embP i ph vs z z' vs2 := by
  obtain ⟨tr, tl, q, nc, dd, hnc, hq, htr, htl, hv, hz⟩ := h
  exact ⟨tr, tl, q, nc, dd, hnc, by rw [htr.rootV_of_prefix hp]; exact hq, htr.mono hp,
    lt_of_lt_of_le htl hp.length_le, by rw [getD_of_prefix hp htl]; exact hv, hz⟩

theorem joined_afterLo {ph : PhT} (h : chainsHaveJoined ph) : chainsHaveJoined ph.afterLo := by cases ph <;> exact h

theorem afterLo_ne_first (ph : PhT) : ph.afterLo ≠ .first := by cases ph <;> simp [PhT.afterLo]

variable {f sMT t cms xin a A w W embS embP i}

/-- A local round, then the rest. -/
theorem slotDone_lo (hk : a.kind = .lo) (hns : a.NoShared) (hw : w.OKG) {ph phE : PhT}
    {vs vs1 vs' : List Bits} {m0 : a.M0} {k0 : a.kind.Sh r.Chal → SStrat s A}
    {t0s : List (Option TTree)} {n0s : List ℕ} {req' : Option TTree} {z : SlotSt lam K Y (r :: s)}
    {z1 : SlotSt lam K Y s} {acc' : SlotAcc lam K Y} (hpre : SlotPre vs ph z.2) (hp : vs <+: vs1)
    (hp' : vs1 <+: vs') (h1 : LoPost f sMT t cms xin a A w embS embP i ph vs z z1 vs1)
    (h2 : SlotDone f sMT t cms xin s A W (fun p => embS (.inr p)) (fun y => embP (.inr y)) (i + 1)
      ph.afterLo phE vs1 (k0 (a.kind.shOf (w.chal (blk0 lam K)))) t0s n0s req' vs' z1 acc') :
    SlotDone f sMT t cms xin (r :: s) (a, A) (w, W) embS embP i ph phE vs (m0, k0) (none :: t0s)
      n0s req' vs' z acc' := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  obtain ⟨tr, tl, q, nc, dd, hnc, hq, htr, htl, hv, rfl⟩ := h1
  obtain ⟨e1, ⟨more, e2⟩, e3, e4, bls, tjs, nJ, e5, e6, e8, e7⟩ := h2
  refine ⟨e1, ⟨tl :: more, by rw [e2]; simp⟩, e3, fun hj => e4 (joined_afterLo hj),
    (f (OracleName.fb t) q).1 :: bls, tr :: tjs, nc.toList ++ nJ, by rw [e5]; simp, by rw [e6]; simp,
    by rw [e8]; cases nc <;> simp, ?_⟩
  rintro ⟨mj, kj⟩ hz salt rtreq hsalt hrt
  have hz' : (m, k) = (a.join m0 mj, fun c => SStrat.zip (k0 (a.kind.shOf c)) (kj c)) := hz
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hz'
  obtain ⟨rts, hR, hE⟩ := e7 (kj (w.chal (f (OracleName.fb t) q).1)) (by
            show SStrat.zip (k0 (a.kind.shOf _)) _ = _
            rw [shOf_lo a hk _ (w.chal (blk0 lam K))]) salt rtreq (fun h => absurd h (afterLo_ne_first ph)) hrt
  refine ⟨((none, some (rootV lam vs' tr)), rts),
    ⟨tr, none, tjs, t0s, rfl, rfl, trivial, (htr.mono hp').compOK, fun _ => hns,
      (fun h => by cases h), (fun _ => hns.1),
      (fun h => own_false_of_noJ hw (htr.has_false h)), hR⟩,
    ?_⟩
  have hact := actOf_lo (L := L) cms vs (acc.x.bind xin) i salt ph acc hpre hsalt
  rw [← hk] at hact
  have hroots : (rootToks (tr :: tjs) (none :: t0s)).map (dv lam vs') =
      (rootV lam vs' tr).toList ++ (rootToks tjs t0s).map (dv lam vs') :=
    map_rootToks_cons vs' tr none tjs t0s
  rw [hroots]
  have hq' : q =
      ⟨i, headLo cms L vs (acc.x.bind xin) i ph acc,
        rootV lam vs' tr,
        embP (.inl (.inr (putO w.grJ nc (a.plain (a.join m0 mj).2).2)))⟩ := by
    rw [htr.rootV_of_prefix hp']
    exact hq
  rw [putB_lo a A w W hk ph nc hnc nJ n0s]
  refine (chainB_own t cms (acc.x.bind xin) salt rtreq a A w W embP i _ _ hact _
      (htr.isSome vs') _).symm ▸ ?_
  rw [headLo_late, Equiv.apply_symm_apply]
  refine hq' ▸ ?_
  refine (evaluates_eager f).bind (evalsTo_ask f (OracleName.fb t) q)
    ((evaluates_eager f).bind (a := some (rhoOf s A W bls, rts, phV vs' phE acc'))
      ?_ ((evaluates_eager f).pure _))
  rw [← hv, ← phV_afterLo hp tl hpre]
  exact hE

end Steps

section Steps2
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq : ℕ)
  {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a) (W : RoundsQueryLayout lam K s A)
  (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
  (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)

/-- Under `a.Coherent`, `w.OKG`: the leaves of the tree over the shared component do not depend on
the slot's component. -/
theorem bodyAt_shared {a : RAnn r} {w : WireRB lam K r a} (hC : a.Coherent) (hw : w.OKG)
    (emb : (p : r.Pos) → r.Sym p → Body L) (m0 : a.M0) (mj mj' : a.Mj) :
    bodyAt w.posAt0 emb (a.join m0 mj).1 = bodyAt w.posAt0 emb (a.join m0 mj').1 := by
  funext l
  unfold bodyAt
  cases h : w.posAt0 l with
  | none => rfl
  | some p => simp only [hC.rd_shared m0 mj mj' p (hw.place_posAt0 l p h).1]

/-- what the joining round ensures for one slot; vs is the store at the start of the round -/
def JoinPost (vs : List Bits) (z z' : SlotSt lam K Y (r :: s)) (vs' : List Bits) : Prop :=
  ∃ (tr : Option TTree) (c : Tok) (q : JoiningRoundQuery lam L t),
    q = ⟨i, vs.getD z.2.tk [], rootV lam vs' tr, embP (.inl (.inr (a.plain z.1.1.2).2))⟩ ∧
    OTreeOK f sMT vs' w.hasJ tr w.depthJ (bodyAt w.posAtJ (fun p => embS (.inl p)) z.1.1.1) ∧
    IsDig lam vs' c ∧
    dv lam vs' c = f (OracleName.g t) q ∧
    z' =
      (z.1, ⟨z.2.x, z.2.tk, c, z.2.blocks, z.2.trees ++ [tr], z.2.toks ++ [c], z.2.nons, z.2.dead⟩)

variable {f sMT t cms xin a A w W embS embP i}

theorem JoinPost.mono {vs : List Bits} {z z' : SlotSt lam K Y (r :: s)} {vs1 vs2 : List Bits}
    (hp : vs1 <+: vs2) (h : JoinPost f sMT t a A w embS embP i vs z z' vs1) :
    JoinPost f sMT t a A w embS embP i vs z z' vs2 := by
  obtain ⟨tr, c, q, hq, htr, hc, hv, hz⟩ := h
  exact ⟨tr, c, q, by rw [htr.rootV_of_prefix hp]; exact hq, htr.mono hp, hc.mono hp,
    by rw [dv_of_prefix hp hc.1]; exact hv, hz⟩

/-- The joining round, then the rest. vs3 is the store after the round. -/
theorem slotDone_join (hk : a.kind = .sh) (hC : a.Coherent) (hw : w.OKG) {phE : PhT}
    {vs vs3 vs' : List Bits} {m0 : a.M0} {k0 : a.kind.Sh r.Chal → SStrat s A}
    {t0s : List (Option TTree)} {n0s : List ℕ} {req' : Option TTree}
    {z z1 : SlotSt lam K Y (r :: s)} {acc' : SlotAcc lam K Y} {rq : TTree} {tr0 : Option TTree}
    {tl : Tok} {q4 : FbIn lam L t} {mjd : a.Mj} {nc : Option ℕ}
    (hnc : nc.isSome = w.gr0.isSome) (hp' : vs3 <+: vs')
    (h1 : JoinPost f sMT t a A w embS embP i vs z z1 vs3) (hrq : IsDig lam vs3 rq.root)
    (htr0 : OTreeOK f sMT vs3 w.has0 tr0 w.depth0
      (bodyAt w.posAt0 (fun p => embS (.inl p)) (a.join m0 mjd).1))
    (hq4 : q4 =
      ⟨i, .f4 cms (vs3.getD rq.root []), rootV lam vs3 tr0,
        embP (.inl (.inl (putO w.gr0 nc (a.pl0 m0))))⟩)
    (hv : vs3.getD tl [] = List.ofFn (f (OracleName.fb t) q4).2) (hreq : req' = some rq)
    (h2 : SlotDone f sMT t cms xin s A W (fun p => embS (.inr p)) (fun y => embP (.inr y)) (i + 1)
      (.shr tl) phE vs3 (k0 (a.kind.shOf (w.chal (f (OracleName.fb t) q4).1))) t0s n0s req' vs'
      (hear w (f (OracleName.fb t) q4).1 true z1) acc') :
    SlotDone f sMT t cms xin (r :: s) (a, A) (w, W) embS embP i .loc phE vs (m0, k0) (tr0 :: t0s)
      (nc.toList ++ n0s) req' vs' z acc' := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  obtain ⟨tr, c, q, hq, htr, hc, hcv, rfl⟩ := h1
  obtain ⟨e1, ⟨more, e2⟩, e3, -, bls, tjs, nJ, e5, e6, e8, e7⟩ := h2
  refine ⟨e1, ⟨c :: more, by rw [e2]; simp [hear]⟩, e3, fun hj => hj.elim,
    (f (OracleName.fb t) q4).1 :: bls, tr :: tjs, nJ, by rw [e5]; simp [hear],
    by rw [e6]; simp [hear], e8, ?_⟩
  rintro ⟨mj, kj⟩ hz salt rtreq - hrt
  have hz' : (m, k) = (a.join m0 mj, fun c => SStrat.zip (k0 (a.kind.shOf c)) (kj c)) := hz
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hz'
  obtain ⟨rts, hR, hE⟩ :=
    e7 (kj (w.chal (f (OracleName.fb t) q4).1)) rfl salt rtreq (fun h => by cases h) hrt
  refine ⟨((some (rootV lam vs' tr0), some (rootV lam vs' tr)), rts),
    ⟨tr, tr0, tjs, t0s, rfl, rfl,
      (by rw [bodyAt_shared hC hw _ m0 mj mjd]; exact (htr0.mono hp').compOK),
      (htr.mono hp').compOK, (fun h => by cases h), (fun h => by cases h),
      (fun h => own_true_of_no0 hw (htr0.has_false h)),
      (fun h => own_false_of_noJ hw (htr.has_false h)), hR⟩,
    ?_⟩
  have hact : actOf cms ((acc.x.bind xin).map L.early) salt a.kind (phV vs .loc acc) =
      some (.join (vs.getD acc.tk [])) := by rw [hk]; rfl
  rw [map_rootToks_cons vs' tr tr0 tjs t0s]
  have hq' : q =
      ⟨i, vs.getD acc.tk [], rootV lam vs' tr,
        embP (.inl (.inr (a.plain (a.join m0 mj).2).2))⟩ := by
    rw [htr.rootV_of_prefix hp']
    exact hq
  have hq4' : q4 =
      ⟨i, .f4 cms (List.ofFn rtreq),
        rootV lam vs' tr0,
        embP (.inl (.inl (putO w.gr0 nc (a.plain (a.join m0 mj).2).1)))⟩ := by
    rw [hrt rq hreq, dv_of_prefix hp' hrq.1, ← hrq.2, htr0.rootV_of_prefix hp', hC.plain_join]
    exact hq4
  rw [putB_sh a A w W hk .loc (Or.inl rfl) tl nc hnc nJ n0s]
  refine (chainB_join t cms (acc.x.bind xin) salt rtreq a A w W embP i _ _ hact _ _ (htr.isSome vs')
      (htr0.isSome vs') _).symm ▸ ?_
  rw [Equiv.apply_symm_apply]
  refine hq' ▸ hq4' ▸ ?_
  refine (evaluates_eager f).bind (evalsTo_ask f (OracleName.g t) q)
    ((evaluates_eager f).bind (evalsTo_ask f (OracleName.fb t) q4)
      ((evaluates_eager f).bind (a := some (rhoOf s A W bls, rts, phV vs' phE acc'))
        ?_ ((evaluates_eager f).pure _)))
  rw [← hv, ← hcv]
  exact hE

/-- A later shared round, then the rest. -/
theorem slotDone_shr (hk : a.kind = .sh) (hC : a.Coherent) (hw : w.OKG) (hns : a.NoSlot) {phE : PhT}
    {vs vs3 vs' : List Bits} {m0 : a.M0} {k0 : a.kind.Sh r.Chal → SStrat s A}
    {t0s : List (Option TTree)} {n0s : List ℕ} {req' : Option TTree} {z : SlotSt lam K Y (r :: s)}
    {acc' : SlotAcc lam K Y} {tr0 : Option TTree} {tk0 tl : Tok} {q5 : FbIn lam L t} {mjd : a.Mj}
    {nc : Option ℕ} (hnc : nc.isSome = w.gr0.isSome) (hpre : SlotPre vs (.shr tk0) z.2)
    (hp : vs <+: vs3) (hp' : vs3 <+: vs')
    (htr0 : OTreeOK f sMT vs3 w.has0 tr0 w.depth0
      (bodyAt w.posAt0 (fun p => embS (.inl p)) (a.join m0 mjd).1))
    (hq5 : q5 =
      ⟨i, .f5 (vs.getD tk0 []), rootV lam vs3 tr0,
        embP (.inl (.inl (putO w.gr0 nc (a.pl0 m0))))⟩)
    (hv : vs3.getD tl [] = List.ofFn (f (OracleName.fb t) q5).2)
    (h2 : SlotDone f sMT t cms xin s A W (fun p => embS (.inr p)) (fun y => embP (.inr y)) (i + 1)
      (.shr tl) phE vs3 (k0 (a.kind.shOf (w.chal (f (OracleName.fb t) q5).1))) t0s n0s req' vs'
      (hear w (f (OracleName.fb t) q5).1 false z) acc') :
    SlotDone f sMT t cms xin (r :: s) (a, A) (w, W) embS embP i (.shr tk0) phE vs (m0, k0)
      (tr0 :: t0s) (nc.toList ++ n0s) req' vs' z acc' := by
  obtain ⟨⟨m, k⟩, acc⟩ := z
  obtain ⟨e1, ⟨more, e2⟩, e3, e4, bls, tjs, nJ, e5, e6, e8, e7⟩ := h2
  refine ⟨e1, ⟨more, e2⟩, e3, fun _ => e4 trivial, (f (OracleName.fb t) q5).1 :: bls, none :: tjs, nJ,
    by rw [e5]; simp [hear], by rw [e6]; simp [hear], e8, ?_⟩
  rintro ⟨mj, kj⟩ hz salt rtreq - hrt
  have hz' : (m, k) = (a.join m0 mj, fun c => SStrat.zip (k0 (a.kind.shOf c)) (kj c)) := hz
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hz'
  obtain ⟨rts, hR, hE⟩ :=
    e7 (kj (w.chal (f (OracleName.fb t) q5).1)) rfl salt rtreq (fun h => by cases h) hrt
  refine ⟨((some (rootV lam vs' tr0), none), rts),
    ⟨none, tr0, tjs, t0s, rfl, rfl,
      (by rw [bodyAt_shared hC hw _ m0 mj mjd]; exact (htr0.mono hp').compOK), trivial,
      (fun h => by cases h), (fun _ => hns),
      (fun h => own_true_of_no0 hw (htr0.has_false h)), (fun _ => hns.1), hR⟩,
    ?_⟩
  have hact : actOf cms ((acc.x.bind xin).map L.early) salt a.kind (phV vs (.shr tk0) acc) =
      some (.one (.f5 (vs.getD tk0 [])) false fun v => .shr v (dv lam vs acc.c)) := by
    rw [hk]; rfl
  have hroots : (rootToks (none :: tjs) (tr0 :: t0s)).map (dv lam vs') =
      (rootV lam vs' tr0).toList ++ (rootToks tjs t0s).map (dv lam vs') :=
    map_rootToks_cons vs' none tr0 tjs t0s
  rw [hroots]
  have hq5' : q5 =
      ⟨i, .f5 (vs.getD tk0 []),
        rootV lam vs' tr0,
        embP (.inl (.inl (putO w.gr0 nc (a.plain (a.join m0 mj).2).1)))⟩ := by
    rw [htr0.rootV_of_prefix hp', hC.plain_join]
    exact hq5
  rw [putB_sh a A w W hk (.shr tk0) (Or.inr ⟨tk0, rfl⟩) tl nc hnc nJ n0s]
  refine (chainB_shared t cms (acc.x.bind xin) salt rtreq a A w W embP i _ _ hact _
      (htr0.isSome vs') _).symm ▸ ?_
  rw [Equiv.apply_symm_apply]
  refine hq5' ▸ ?_
  refine (evaluates_eager f).bind (evalsTo_ask f (OracleName.fb t) q5)
    ((evaluates_eager f).bind (a := some (rhoOf s A W bls, rts, phV vs' phE acc'))
      ?_ ((evaluates_eager f).pure _))
  rw [← hv, ← dv_of_prefix hp hpre.2.1]
  exact hE

end Steps2

section Main
variable {Y : Type} (sMT : ℕ) (t : Tag) (cms : List (Dig lam)) (xin : Y → Option X) (depthReq : ℕ)

theorem forall₂_mem_right {α β : Type} {P : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → ∀ b ∈ l₂, ∃ a ∈ l₁, P a b
  | _, _, .nil, _, h => by cases h
  | _, _, .cons h1 t1, b, h => by
      rcases List.mem_cons.1 h with rfl | h
      · exact ⟨_, List.mem_cons_self, h1⟩
      · obtain ⟨a, ha, hab⟩ := forall₂_mem_right t1 b h
        exact ⟨a, List.mem_cons_of_mem _ ha, hab⟩

theorem forall₂_map_eq {α β γ : Type} {P : α → β → Prop} (g : α → γ)
    (g' : β → γ) (h : ∀ a b, P a b → g' b = g a) :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ P l₁ l₂ → l₂.map g' = l₁.map g
  | _, _, .nil => rfl
  | _, _, .cons h1 t1 => by rw [List.map_cons, List.map_cons, h _ _ h1, forall₂_map_eq g g' h t1]

variable {f depthReq} in
/-- under the hypotheses below: the request tree stays correct when the store grows and the slot
values stay -/
theorem ReqInv.step {vs vs' : List Bits} (hp : vs <+: vs') {ph ph' : PhT} {req : Option TTree}
    {cs cs' : List Tok} (h : ReqInv f depthReq vs ph req cs) (hj : chainsHaveJoined ph' ↔ chainsHaveJoined ph)
    (hcs : cs' = cs) (hd : chainsHaveJoined ph → ∀ c ∈ cs, IsDig lam vs c) :
    ReqInv f depthReq vs' ph' req cs' := by
  subst hcs
  refine ⟨fun hn => h.1 fun hh => hn (hj.2 hh), fun hh => ?_⟩
  obtain ⟨rq, h1, h2, h3⟩ := h.2 (hj.1 hh)
  exact ⟨rq, h1, by rw [map_dv_of_prefix hp (hd (hj.1 hh))]; exact h2.mono hp, h3⟩

theorem joined_afterLo_iff (ph : PhT) : chainsHaveJoined ph.afterLo ↔ chainsHaveJoined ph := by
  cases ph <;> exact Iff.rfl

theorem isDig_c_of_pre {vs : List Bits} :
    ∀ {ph : PhT} {acc : SlotAcc lam K Y}, SlotPre vs ph acc → chainsHaveJoined ph → IsDig lam vs acc.c
  | .shr _, _, h, _ => h.2
  | .aft, _, h, _ => h.2

section Join
variable {r : Round} {s : Shape} (a : RAnn r) (A : RoundSplits s) (w : WireRB lam K r a)
  (embS : (p : OPos (r :: s)) → OSym (r :: s) p → Body L)
  (embP : PlainPart (r :: s) (a, A) → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ)

/-- the joining round in all slots; vs0 is the store at the start of the round -/
theorem tri_joinM (vs0 : List Bits) :
    ∀ (zs : List (SlotSt lam K Y (r :: s))) (vs : List Bits), vs0 <+: vs →
      (∀ z ∈ zs, z.2.tk < vs0.length) →
      Tri f (joinM sMT t a w (fun p => embS (.inl p)) (fun α => embP (.inl (.inr α))) i zs) vs
        fun o vs' =>
      List.Forall₂ (fun z z' => JoinPost f sMT t a A w embS embP i vs0 z z' vs') zs o.1 ∧
      o.2 = o.1.map fun z => z.2.c
  | [], _, _, _ => tri_pure_iff.2 ⟨.nil, rfl⟩
  | ⟨⟨m, k⟩, acc⟩ :: zs, vs, hp, h => by
      have hz : acc.tk < vs0.length := h ⟨⟨m, k⟩, acc⟩ (by simp)
      refine Tri.bind
        (tri_slotJoin f sMT t a w _ _ i m k acc vs (lt_of_lt_of_le hz hp.length_le)).with_prefix
        fun z' vs1 hz' => ?_
      refine Tri.bind
        (tri_joinM vs0 zs vs1 (hp.trans hz'.2) fun u hu => h u (by simp [hu])).with_prefix
        fun o vs2 ho => tri_pure_iff.2 ⟨.cons ?_ ho.1.1, ?_⟩
      · obtain ⟨tr, c, q, hq, htr, hc, hcv, rfl⟩ := hz'.1
        exact JoinPost.mono ho.2
          ⟨tr, c, q, by rw [← getD_of_prefix hp hz]; exact hq, htr, hc, hcv, rfl⟩
      · show z'.2.c :: o.2 = _
        rw [ho.1.2]
        rfl

end Join

/-- The chain, under `RealFam` and the hypotheses below. Whatever the coins: after all rounds, for
every slot whose strategy is the shared strategy with one of its own, the verifier's chain
recomputes the slot's verifier messages, and the slot's trees and the shared ones are kept correctly
(`RoundsOK`); the request tree, if there is one, is the tree over the slot values of all slots. -/
theorem tri_chainT (hf : RealFam f) :
    ∀ (s : Shape) (A : RoundSplits s) (W : RoundsQueryLayout lam K s A) (embS : (p : OPos s) → OSym s p → Body L)
    (embP : PlainPart s A → PlainPart (shapeOf L t) (annOf L t)) (i : ℕ) (ph : PhT) (σ0 : SStrat s A)
    (zs : List (SlotSt lam K Y s)) (a0 : Acc0) (vs : List Bits),
    RoundsQueryLayout.OKG s A W → A.Coherent → RoundSplits.FmtFrom s A (fph ph) →
    (zs.length = 2 ^ depthReq ∨ AllLo s A) → (∀ z ∈ zs, SlotPre vs ph z.2) →
    ReqInv f depthReq vs ph a0.req (zs.map fun z => z.2.c) →
    Tri f (chainT sMT t cms xin depthReq s A W embS embP i ph σ0 zs a0) vs fun out vs' =>
      ∃ (phE : PhT) (t0s : List (Option TTree)) (n0s : List ℕ),
        out.2.trees = a0.trees ++ t0s ∧
        out.2.nons = n0s.reverse ++ a0.nons ∧
        ReqInv f depthReq vs' phE out.2.req (out.1.map fun acc => acc.c) ∧
        (chainsHaveJoined ph → out.2.req = a0.req) ∧
        List.Forall₂
          (SlotDone f sMT t cms xin s A W embS embP i ph phE vs σ0 t0s n0s out.2.req vs') zs out.1
  | [], _, _, _, _, _, ph, _, zs, a0, vs, _, _, _, _, hpre, hreq => by
      refine tri_pure_iff.2
        ⟨ph, [], [], by simp, by simp, by simpa [List.map_map] using hreq, fun _ => rfl, ?_⟩
      refine (List.forall₂_map_right_iff).2 ((List.forall₂_same).2 fun z hz => ?_)
      exact ⟨rfl, ⟨[], by simp⟩, hpre z hz, fun _ => rfl, [], [], [], by simp, by simp, by simp,
        fun _ _ _ _ _ _ => ⟨(), ⟨rfl, rfl⟩, rfl⟩⟩
  | r :: s, (a, A), (w, W), embS, embP, i, ph, (m0, k0), zs, a0, vs, hW, hC, hF, hN, hpre, hreq => by
      have hF2 : (match a.kind, fph ph with
          | .lo, ph => a.NoShared ∧ RoundSplits.FmtFrom s A ph.afterLo
          | .sh, .loc => RoundSplits.FmtFrom s A .shr
          | .sh, .shr => a.NoSlot ∧ RoundSplits.FmtFrom s A .shr
          | .sh, .first => False
          | .sh, .aft => False) := hF
      by_cases hk : a.kind = .lo
      · -- a local round
        rw [hk] at hF2
        rw [chainT_lo sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk ph]
        refine Tri.bind
          ((tri_eachM (f := f) _
            (fun (z : SlotSt lam K Y (r :: s)) v => vs <+: v ∧ SlotPre vs ph z.2)
            (fun (z : SlotSt lam K Y (r :: s)) (z' : SlotSt lam K Y s) v =>
              SlotPre vs ph z.2 ∧ LoPost f sMT t cms xin a A w embS embP i ph vs z z' v)
            (fun z v v' hp h => ⟨h.1.trans hp, h.2⟩) (fun z z' v v' hp h => ⟨h.1, h.2.mono hp⟩)
            ?_ zs vs (fun z hz => ⟨List.prefix_refl _, hpre z hz⟩)).with_prefix)
          fun zs1 vs1 h1 => ?_
        · rintro ⟨⟨m, k⟩, acc⟩ v ⟨hpv, hz⟩
          refine (tri_slotLo f sMT t cms xin a w _ _ i hf ph m k acc v (hz.mono hpv)).mono ?_
          rintro z' v' ⟨tr, tl, q, nc, dd, hnc, hq, htr, htl, hv, rfl⟩
          exact ⟨hz, tr, tl, q, nc, dd, hnc,
            by rw [← headLo_of_prefix cms hpv _ _ hz]; exact hq, htr, htl, hv, rfl⟩
        · obtain ⟨h1, hp⟩ := h1
          have hcs : (zs1.map fun z => z.2.c) = zs.map fun z => z.2.c :=
            forall₂_map_eq (fun z => z.2.c) (fun z => z.2.c) (fun z z1 hz => by
              obtain ⟨-, tr, tl, q, nc, dd, -, -, -, -, -, rfl⟩ := hz
              rfl) h1
          refine ((tri_chainT hf s A W _ _ (i + 1) ph.afterLo _ zs1
            { a0 with trees := a0.trees ++ [none] } vs1 hW.2 hC.2
            (by rw [fph_afterLo]; exact hF2.2)
            (hN.imp (fun h => by rw [← h1.length_eq]; exact h) fun h => h.2) ?_
            (hreq.step hp (joined_afterLo_iff ph) hcs fun hj c hc => by
              obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hc
              exact isDig_c_of_pre (hpre z hz) hj)).with_prefix).mono ?_
          · intro z1 hz1
            obtain ⟨z, -, hz, tr, tl, q, nc, dd, -, -, -, htl, -, rfl⟩ :=
              forall₂_mem_right h1 z1 hz1
            exact slotPre_afterLo hp htl hz _ _ _ _ _
          · rintro out vs' ⟨⟨phE, t0s, n0s, e1, e0, e2, e3, e4⟩, hp'⟩
            exact ⟨phE, none :: t0s, n0s, by rw [e1]; simp, e0,
              e2, fun hj => e3 (joined_afterLo hj),
              forall₂_comp
                (fun z z1 acc' hz1 hz2 => slotDone_lo hk hF2.1 hW.1 hz1.1 hp hp' hz1.2 hz2) h1 e4⟩
      · have hk' : a.kind = .sh := by
          cases h : a.kind with
          | lo => exact absurd h hk
          | sh => rfl
        rw [hk'] at hF2
        have hlen : zs.length = 2 ^ depthReq := hN.resolve_right fun h => hk h.1
        cases ph with
        | first => exact False.elim hF2
        | aft => exact False.elim hF2
        | loc =>
          -- the joining round
          rw [chainT_join sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk']
          refine Tri.bind
            (tri_joinM f sMT t a A w embS embP i vs zs vs (List.prefix_refl _) hpre).with_prefix
            fun o vs1 ho => ?_
          obtain ⟨⟨ho1, ho2⟩, hp1⟩ := ho
          have hdig : ∀ c ∈ o.2, IsDig lam vs1 c := by
            intro c hc
            rw [ho2] at hc
            obtain ⟨z1, hz1, rfl⟩ := List.mem_map.1 hc
            obtain ⟨z, -, tr, c, q, -, -, hcd, -, rfl⟩ := forall₂_mem_right ho1 z1 hz1
            exact hcd
          refine Tri.bind (tri_reqT f depthReq o.2 vs1 hdig).with_prefix fun rq vs2 hrq => ?_
          refine tri_withTree f sMT w.has0 w.depth0 _ _ vs2 _ fun tr0 vs2a hp2a htr0a => ?_
          obtain ⟨hrq, hp2⟩ := hrq
          have hlen1 : o.2.length = 2 ^ depthReq := by
            rw [ho2, List.length_map, ← ho1.length_eq]; exact hlen
          have hrqd : IsDig lam vs2 rq.root := hrq.isDig_root (by simpa using hlen1)
          refine tri_fbG f t i hf w.gr0 w.chal _ _ tr0 _ _ _ _ _ vs2a _
            (Head.f4 cms (vs2a.getD rq.root [])) (rootV lam vs2a tr0)
            (fun v hv => ⟨by rw [getD_of_prefix hv (hrqd.mono hp2a).1], htr0a.rootV_of_prefix hv⟩)
            fun nc dd vs2' hpb hnc => ?_
          have hp2' : vs2 <+: vs2' := hp2a.trans hpb
          have htr0 := htr0a.mono hpb
          rw [← getD_of_prefix hpb (hrqd.mono hp2a).1, ← htr0a.rootV_of_prefix hpb]
          generalize hq4 : (⟨i, Head.f4 cms (vs2'.getD rq.root []), rootV lam vs2' tr0,
            embP (.inl (.inl (putO w.gr0 nc (a.pl0 m0))))⟩ : FbIn lam L t) = q4
          have hp3 : vs2' <+: vs2' ++ [List.ofFn (f (OracleName.fb t) q4).2] := List.prefix_append _ _
          have hcs : ((o.1.map (hear w (f (OracleName.fb t) q4).1 true)).map fun z => z.2.c) = o.2 := by
            rw [ho2, List.map_map]
            exact List.map_congr_left fun z _ => rfl
          refine ((tri_chainT hf s A W _ _ (i + 1) (.shr vs2'.length)
            (k0 (a.kind.shOf (w.chal (f (OracleName.fb t) q4).1)))
            (o.1.map (hear w (f (OracleName.fb t) q4).1 true))
            ⟨a0.trees ++ [tr0], a0.toks ++ [vs2'.length], some rq,
              nc.toList ++ a0.nons, dd ++ a0.dead⟩
            (vs2' ++ [List.ofFn (f (OracleName.fb t) q4).2]) hW.2 hC.2 hF2
            (Or.inl (by rw [List.length_map, ← ho1.length_eq]; exact hlen)) ?_
            ⟨fun hn => absurd trivial hn,
              fun _ => ⟨rq, rfl, ?_, by rw [hcs]; exact hlen1⟩⟩).with_prefix).mono ?_
          · intro z' hz'
            obtain ⟨z1, hz1, rfl⟩ := List.mem_map.1 hz'
            obtain ⟨z, -, tr, c, q, -, -, hcd, -, rfl⟩ := forall₂_mem_right ho1 z1 hz1
            exact ⟨by simp, hcd.mono (hp2.trans (hp2'.trans hp3))⟩
          · rw [hcs, map_dv_of_prefix (hp2.trans (hp2'.trans hp3)) hdig]
            exact hrq.mono (hp2'.trans hp3)
          · rintro out vs' ⟨⟨phE, t0s, n0s, e1, e0, e2, e3, e4⟩, hp'⟩
            refine ⟨phE, tr0 :: t0s, nc.toList ++ n0s, by rw [e1]; simp,
              by rw [e0]; cases nc <;> simp, e2, fun hj => hj.elim, ?_⟩
            refine forall₂_comp
              (fun z z1 acc' hz1 hz2 =>
                slotDone_join hk' hC.1 hW.1 hnc hp'
                  (hz1.mono (hp2.trans (hp2'.trans hp3))) (hrqd.mono (hp2'.trans hp3))
                  (htr0.mono hp3) ?_ (getD_concat_length _ _) (e3 trivial) hz2)
              ho1 ((List.forall₂_map_left_iff).1 e4)
            rw [getD_of_prefix hp3 (hrqd.mono hp2').1, htr0.rootV_of_prefix hp3, ← hq4]
        | shr tk0 =>
          -- a later shared round
          rw [chainT_shr sMT t cms xin depthReq a A w W embS embP i m0 k0 zs a0 hk' tk0]
          refine tri_withTree f sMT w.has0 w.depth0 _ _ vs _ fun tr0 vs2a hp2a htr0a => ?_
          have htk0 : zs ≠ [] → tk0 < vs.length := fun hne => by
            obtain ⟨z, hz⟩ := List.exists_mem_of_ne_nil zs hne
            exact (hpre z hz).1
          have hzs : zs ≠ [] := fun h0 => by
            rw [h0] at hlen
            exact absurd hlen.symm (Nat.pos_iff_ne_zero.1 (Nat.pow_pos (by norm_num)))
          refine tri_fbG f t i hf w.gr0 w.chal _ _ tr0 _ _ _ _ _ vs2a _
            (Head.f5 (vs2a.getD tk0 [])) (rootV lam vs2a tr0)
            (fun v hv =>
              ⟨by rw [getD_of_prefix hv (lt_of_lt_of_le (htk0 hzs) hp2a.length_le)],
                htr0a.rootV_of_prefix hv⟩)
            fun nc dd vs2 hpb hnc => ?_
          have hp2 : vs <+: vs2 := hp2a.trans hpb
          have htr0 := htr0a.mono hpb
          rw [← getD_of_prefix hpb (lt_of_lt_of_le (htk0 hzs) hp2a.length_le),
            ← htr0a.rootV_of_prefix hpb]
          generalize hq5 : (⟨i, Head.f5 (vs2.getD tk0 []), rootV lam vs2 tr0,
            embP (.inl (.inl (putO w.gr0 nc (a.pl0 m0))))⟩ : FbIn lam L t) = q5
          have hp3 : vs2 <+: vs2 ++ [List.ofFn (f (OracleName.fb t) q5).2] := List.prefix_append _ _
          have hcs : ((zs.map (hear w (f (OracleName.fb t) q5).1 false)).map fun z => z.2.c) =
              zs.map fun z => z.2.c := by
            rw [List.map_map]
            exact List.map_congr_left fun z _ => rfl
          refine ((tri_chainT hf s A W _ _ (i + 1) (.shr vs2.length)
            (k0 (a.kind.shOf (w.chal (f (OracleName.fb t) q5).1)))
            (zs.map (hear w (f (OracleName.fb t) q5).1 false))
            { a0 with
              trees := a0.trees ++ [tr0], toks := a0.toks ++ [vs2.length],
              nons := nc.toList ++ a0.nons, dead := dd ++ a0.dead }
            (vs2 ++ [List.ofFn (f (OracleName.fb t) q5).2])
            hW.2 hC.2 hF2.2 (Or.inl (by rw [List.length_map]; exact hlen)) ?_
            (hreq.step (hp2.trans hp3) Iff.rfl hcs fun _ c hc => by
              obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hc
              exact (hpre z hz).2)).with_prefix).mono ?_
          · intro z' hz'
            obtain ⟨z, hz, rfl⟩ := List.mem_map.1 hz'
            exact ⟨by simp, (hpre z hz).2.mono (hp2.trans hp3)⟩
          · rintro out vs' ⟨⟨phE, t0s, n0s, e1, e0, e2, e3, e4⟩, hp'⟩
            refine ⟨phE, tr0 :: t0s, nc.toList ++ n0s, by rw [e1]; simp,
              by rw [e0]; cases nc <;> simp, e2, fun _ => e3 trivial, ?_⟩
            have h0 : List.Forall₂
                (fun (z z1 : SlotSt lam K Y (r :: s)) => SlotPre vs (.shr tk0) z.2 ∧ z1 = z)
                zs zs :=
              (List.forall₂_same).2 fun z hz => ⟨hpre z hz, rfl⟩
            refine forall₂_comp (fun z z1 acc' hz1 hz2 => ?_) h0 ((List.forall₂_map_left_iff).1 e4)
            obtain ⟨hz, rfl⟩ := hz1
            refine slotDone_shr hk' hC.1 hW.1 hF2.1 hnc hz (hp2.trans hp3) hp' (htr0.mono hp3) ?_
              (getD_concat_length _ _) hz2
            rw [← getD_of_prefix hp2 hz.1, htr0.rootV_of_prefix hp3, ← hq5]

end Main

end Compile.Batch.Cmpl
