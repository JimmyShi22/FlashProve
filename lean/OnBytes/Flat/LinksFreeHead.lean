-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Flat/LinksFreeHead.lean: the check of the head at two requests (`HeadFree`,
OnBytes/Flat/LinksFree.lean), cut into seven pieces.

How the request goes through the check (`Head.runForkHidH2`, OnBytes/Model/Head.lean), by the
program's text. It enters as the covered positions `cov`. `hear` lays the checked tokens into what
it returns; `tablesOf` makes the weights of three tables of reads from it; these tables go into the
state of the smallness test (`closeFuns`); `weightsClaim` makes one factor of the claim on the
weights from it. Up to there the state of the check is the same at both requests. `walk` adds the
claims: from `claimJoin` on some hold a value made of the request, and the states are only alike
(`ForkAlike`, OnBytes/Flat/LinksFreeFork.lean). So the two runs are compared in two stretches: from
one state with equal states left (`cmpL`), and from states that are alike (`cmpLA`); `fromEq` joins
them.

The relations: `CovAlike` (four arrays of the same sizes), `HeardAlike`, `FunAlike`, `FunsAlike`,
`TablesAlike`, `RunAlike`, `TailAlike f f'` (two states of the smallness test: all is equal but the
list of tables, which is f in the first and f' in the second).

The seven pieces, each a definition by name: `HearFree`, `TablesFree`, `TranscriptFree`,
`WeightsClaimFree` (equal states); `WalkFree` (from one state to states that are alike);
`SelfTestsFree`, `DoorFree` (states that are alike).

Main theorems: `fromEq_bind`, `fromEq_then`, `fromEq_of`; `relB_testAs`; `runForkHidH2_rel`;
`samePlan_alike`, `covered_sizes`; `headFree_of`: `HeadFree p` from the seven, at every p.

Not claimed: any of the seven pieces. Nothing on a run on a view. For proofs only; no module of the
program imports this file.


-/
import OnBytes.Flat.LinksRespBank

set_option autoImplicit false

namespace OnBytes.Flat

open OnBytes.Model OnBytes.Model.Head

/-- Closes `Blk.Keeps b` by the walk. -/
local macro "keeps_blk" : tactic => `(tactic| (show Over.K (m := Blk) _; keeps))

/-! ## The relations -/

/-- The covered positions of two requests: the four arrays have the same sizes. -/
def CovAlike (c c' : Covered) : Prop :=
  c.tokv.size = c'.tokv.size ∧ c.hOn.size = c'.hOn.size ∧ c.hWin.size = c'.hWin.size ∧
    c.hOnC.size = c'.hOnC.size

/-- What was received and drawn: all is equal but the checked tokens, of which there are as many. -/
def HeardAlike (x x' : Heard) : Prop := x' = { x with win := x'.win } ∧ x.win.size = x'.win.size

/-- Two tables of reads: all is equal but the weights, of which there are as many. -/
def FunAlike (f f' : HFun) : Prop := f' = { f with phi := f'.phi } ∧ f.phi.size = f'.phi.size

/-- Two lists of tables. -/
def FunsAlike (a a' : Array HFun) : Prop := All2 FunAlike a.toList a'.toList

def TablesAlike (t t' : Tables) : Prop := t' = { t with funs := t'.funs } ∧ FunsAlike t.funs t'.funs

/-- All that the claims are made from, at two requests. -/
def RunAlike (R R' : Head.Run) : Prop :=
  R' = { R with cov := R'.cov, x := R'.x, t := R'.t } ∧ CovAlike R.cov R'.cov ∧
    HeardAlike R.x R'.x ∧ TablesAlike R.t R'.t

/-- Two states of the smallness test that hold the lists f and f': all is equal but the list of
tables. -/
def TailAlike (f f' : Array HFun) (tl tl' : HTailF2) : Prop :=
  tl.funs = f ∧ tl' = { tl with funs := f' }

/-! ## From one state to states that are alike -/

/-- Two routines of a link, from one context of the link and ONE state: values in R, one context of
the link left, states that are alike. -/
def fromEq {α : Type} (R : α → α → Prop) (x x' : LinkM α) : Prop :=
  ∀ (C : LinkCtx) (F : Fork),
    relB (fun p p' => (R p.1.1 p'.1.1 ∧ p.1.2 = p'.1.2) ∧ ForkAlike p.2 p'.2) (x C F) (x' C F)

/-- As long as the states are equal. -/
theorem fromEq_bind {α β : Type} {S : α → α → Prop} {R : β → β → Prop} {x x' : LinkM α}
    {f f' : α → LinkM β} (hk : Over.K x) (hx : cmpL.Rel S x x')
    (hf : ∀ a a', S a a' → fromEq R (f a) (f' a')) : fromEq R (x >>= f) (x' >>= f') := by
  intro C F
  show relB _ (x C F >>= fun q => f q.1.1 q.1.2 q.2) (x' C F >>= fun q => f' q.1.1 q.1.2 q.2)
  refine relB_bind (hk C F) (hx C C rfl F F rfl) fun p p' h => ?_
  obtain ⟨⟨a, C1⟩, F1⟩ := p
  obtain ⟨⟨a', C2⟩, F2⟩ := p'
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h2' : C1 = C2 := h2
  have h3' : F1 = F2 := h3
  subst h2' h3'
  exact hf a a' h1 C1 F1

theorem fromEq_same {α β : Type} {R : β → β → Prop} {x : LinkM α} {f f' : α → LinkM β}
    (hk : Over.K x) (hf : ∀ a, fromEq R (f a) (f' a)) : fromEq R (x >>= f) (x >>= f') :=
  fromEq_bind hk (same_cmpL x) fun a a' e => by subst e; exact hf a

/-- From where the states may differ. -/
theorem fromEq_of {α : Type} {R : α → α → Prop} {x x' : LinkM α} (h : cmpLA.Rel R x x') :
    fromEq R x x' := fun C F => h C C rfl F F (ForkAlike.refl F)

/-- After two routines that leave states alike. -/
theorem fromEq_then {α β : Type} {S : α → α → Prop} {R : β → β → Prop} {x x' : LinkM α}
    {f f' : α → LinkM β} (hk : Over.K x) (hx : fromEq S x x')
    (hf : ∀ a a', S a a' → cmpLA.Rel R (f a) (f' a')) : fromEq R (x >>= f) (x' >>= f') := by
  intro C F
  show relB _ (x C F >>= fun q => f q.1.1 q.1.2 q.2) (x' C F >>= fun q => f' q.1.1 q.1.2 q.2)
  refine relB_bind (hk C F) (hx C F) fun p p' h => ?_
  obtain ⟨⟨a, C1⟩, F1⟩ := p
  obtain ⟨⟨a', C2⟩, F2⟩ := p'
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h2' : C1 = C2 := h2
  subst h2'
  exact hf a a' h1 C1 C1 rfl F1 F2 h3

/-! ## Lifts -/

theorem liftS_cmpL {α : Type} {R : α → α → Prop} {x x' : SubM α} (hk : Over.K x)
    (hx : cmpS.Rel R x x') : cmpL.Rel R (liftM x : LinkM α) (liftM x') := cmpS.lift Eq hk hx

theorem liftS_cmpLA {α : Type} {R : α → α → Prop} {x x' : SubM α} (hk : Over.K x)
    (hx : cmpA.Rel R x x') : cmpLA.Rel R (liftM x : LinkM α) (liftM x') := cmpA.lift Eq hk hx

theorem liftB_cmpL {α : Type} {R : α → α → Prop} {b b' : Blk α} (hk : Blk.Keeps b)
    (hb : relB R b b') : cmpL.Rel R (liftM b : LinkM α) (liftM b') :=
  cmpS.lift Eq (k_lift (m := Blk) hk) (Cmp.blk.lift Eq hk hb)

theorem liftB_cmpLA {α : Type} {R : α → α → Prop} {b b' : Blk α} (hk : Blk.Keeps b)
    (hb : relB R b b') : cmpLA.Rel R (liftM b : LinkM α) (liftM b') :=
  cmpA.lift Eq (k_lift (m := Blk) hk) (Cmp.blk.lift ForkAlike hk hb)

/-- A condition on values is idle in a dry run. -/
theorem relB_testAs (name : String) (b b' : Bool) : relB Eq (testAs name b) (testAs name b') := by
  intro c hc
  have e : ∀ b : Bool, testAs name b c = .ok ((), c) := by
    intro b
    unfold testAs
    show (Blk.isDry >>= fun d => if (b || d) = true then pure () else refuse name) c = _
    rw [Blk.bind_ok (show Blk.isDry c = .ok (c.ch.dry, c) from rfl), hc.1]
    simp only [Bool.or_true, if_true]
    rfl
  rw [e, e]
  exact ⟨rfl, rfl⟩

theorem getAs_rel {α : Type} {R : α → α → Prop} (name : String) {o o' : Option α}
    (h : OptRel R o o') : relB R (getAs name o) (getAs name o') := by
  cases o <;> cases o'
  · exact fun _ _ => trivial
  · exact h.elim
  · exact h.elim
  · exact relB_pure h

/-! ## The pieces, each a statement by name -/

/-- Of the messages up to the commitment to the reads. -/
def HearFree : Prop :=
  ∀ (h : Shape) (L : HL) (hp : HPlanH2) (cov cov' : Covered) (plain : Array E), CovAlike cov cov' →
    cmpS.Rel HeardAlike (hear h L hp cov plain) (hear h L hp cov' plain)

/-- Of the tables of reads. -/
def TablesFree : Prop :=
  ∀ (h : Shape) (L : HL) (hp : HPlanH2) (cov cov' : Covered) (x x' : Heard), CovAlike cov cov' →
    HeardAlike x x' → cmpS.Rel TablesAlike (tablesOf h L hp cov x) (tablesOf h L hp cov' x')

/-- Of the messages of the smallness test. -/
def TranscriptFree : Prop :=
  ∀ (f f' : Array HFun) (tl tl' : HTailF2), FunsAlike f f' → TailAlike f f' tl tl' →
    cmpL.Rel (TailAlike f f') tl.transcript tl'.transcript

/-- Of the one claim on the committed weights. -/
def WeightsClaimFree : Prop :=
  ∀ (R R' : Head.Run) (wsLay : WsLay), RunAlike R R' →
    cmpS.Rel ClaimAlike (weightsClaim R wsLay) (weightsClaim R' wsLay)

/-- Of the walk that adds all claims: from one state to states that are alike. -/
def WalkFree : Prop :=
  ∀ (R R' : Head.Run) (tl tl' : HTailF2) (wo wo' : WsForkOut), RunAlike R R' →
    TailAlike R.t.funs R'.t.funs tl tl' → OutAlike wo wo' →
    fromEq (TailAlike R.t.funs R'.t.funs) (walk R tl wo) (walk R' tl' wo')

/-- Of the tests of the verifier's own walk. -/
def SelfTestsFree : Prop :=
  ∀ (R R' : Head.Run) (tl tl' : HTailF2) (wo wo' : WsForkOut), RunAlike R R' →
    TailAlike R.t.funs R'.t.funs tl tl' → OutAlike wo wo' →
    cmpLA.Rel Eq (selfTests R tl wo) (selfTests R' tl' wo')

/-- Of the link's end, where the one equation goes to the chain. -/
def DoorFree : Prop := ∀ n : Nat, Resp.K (doorH n)

/-- The state of the sub-proof's engine, read at two states that are alike. -/
theorem fork_rel : cmpLA.Rel ForkAlike LinkM.fork LinkM.fork := by
  intro C C' hC
  subst hC
  exact cmpA.bind' (by keeps) (ask_rel (R := ForkAlike) fun _ _ h => h)
    fun _ _ h => cmpA.pure' ⟨h, rfl⟩

theorem runForkHidH2_rel (h1 : HearFree) (h2 : TablesFree) (h3 : TranscriptFree)
    (h4 : WeightsClaimFree) (h5 : WalkFree) (h6 : SelfTestsFree) (h7 : DoorFree) (h : Shape)
    (L : HL) (b : Border) (hp : HPlanH2) (O : Owner)
    {cov cov' : Covered} (hc : CovAlike cov cov') (wsLay : WsLay) :
    fromEq OutAlike (runForkHidH2 h L b hp O cov wsLay) (runForkHidH2 h L b hp O cov' wsLay) := by
  unfold runForkHidH2
  have e : cov'.sized h.T = cov.sized h.T := by
    unfold Covered.sized
    rw [hc.1, hc.2.1, hc.2.2.1, hc.2.2.2]
  rw [e]
  iterate 7 (refine fromEq_same (by keeps) fun _ => ?_)
  rename_i iU3
  refine fromEq_bind (by keeps) (liftS_cmpL (by keeps) (h1 _ _ _ _ _ _ hc)) fun x x' hx => ?_
  obtain ⟨ex, hw⟩ := hx
  generalize x'.win = w' at ex hw
  subst ex
  refine fromEq_same (by keeps) fun _ => ?_
  refine fromEq_bind (by keeps) (liftS_cmpL (by keeps) (h2 _ _ _ _ _ _ _ hc ⟨rfl, hw⟩))
    fun t t' ht => ?_
  obtain ⟨et, hf⟩ := ht
  generalize t'.funs = f' at et hf
  subst et
  dsimp only
  refine fromEq_bind (S := TailAlike t.funs f') (by keeps)
    (liftB_cmpL (by keeps_blk) (getAs_rel _ ?_)) fun tl tl' htl => ?_
  · unfold HTailF2.closeFuns
    split
    · trivial
    · exact ⟨rfl, rfl⟩
  refine fromEq_bind (by keeps) (h3 _ _ _ _ hf htl) fun tl tl' htl => ?_
  have hR : RunAlike { h := h, L := L, b := b, hp := hp, cov := cov, x := x, t := t, iU3 := iU3 }
      { h := h, L := L, b := b, hp := hp, cov := cov', x := { x with win := w' },
        t := { t with funs := f' }, iU3 := iU3 } := ⟨rfl, hc, ⟨rfl, hw⟩, ⟨rfl, hf⟩⟩
  refine fromEq_bind (by keeps) (liftS_cmpL (by keeps) (h4 _ _ wsLay hR)) fun cl cl' hcl => ?_
  refine fromEq_same (by keeps) fun _ => ?_
  refine fromEq_bind (by keeps)
    (liftS_cmpL (by keeps) (wsForkEnd_rel wsLay (l := [cl]) (l' := [cl']) (.cons hcl .nil) _))
    fun wo wo' hwo => ?_
  iterate 4 (refine fromEq_same (by keeps) fun _ => ?_)
  refine fromEq_then (by keeps) (h5 _ _ _ _ _ _ hR htl hwo) fun tl tl' htl => ?_
  refine cmpLA.bind' (by keeps) (h6 _ _ _ _ _ _ hR htl hwo) fun _ _ _ => ?_
  obtain ⟨-, etl⟩ := htl
  subst etl
  refine cmpLA.bind' (S := Eq) (by keeps) (resp_link (by resp)).2 fun n n' en => ?_
  subst en
  refine cmpLA.bind' (by keeps) (resp_link (h7 n)).2 fun _ _ _ => ?_
  refine cmpLA.bind' (by keeps) fork_rel fun F F' hF => ?_
  rw [show (F'.nClaim == F'.planClaimsF) = (F.nClaim == F.planClaimsF) by rw [hF.1]]
  refine cmpLA.bind' (S := Eq) (by keeps) (resp_link (by resp)).2 fun _ _ _ => ?_
  refine cmpLA.bind' (S := Eq) (by keeps) (resp_link (by resp)).2 fun _ _ _ => ?_
  refine cmpLA.bind' (S := Eq) (by keeps) (resp_link (by resp)).2 fun _ _ _ => ?_
  exact cmpLA.pure' hwo

/-! ## The statement on the head, from the pieces -/

theorem samePlan_alike {F F' : Fork} (h : ForkAlike F F') (X : Stages.LinkH) (l : Tail2) :
    Stages.samePlan X F l = Stages.samePlan X F' l := by
  have key : ∀ t : Nat, F.trees[t]?.map (fun a => (a.R, a.K)) =
      F'.trees[t]?.map (fun a => (a.R, a.K)) := fun t =>
    trees_read h.2 (fun o => o.map fun a => (a.R, a.K)) (fun o => by cases o <;> rfl) t
  unfold Stages.samePlan
  refine congrArg (fun z => (l.nt == X.Tp.nt && (List.range X.Tp.nt.size).all z))
    (funext fun t => ?_)
  have k := key t
  revert k
  cases F.trees[t]? <;> cases F'.trees[t]? <;> intro k
  · rfl
  · cases k
  · cases k
  · simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at k
    cases X.Fp.trees[t]? with
    | none => rfl
    | some b => simp only [k.1, k.2]

theorem runFree_of_fromEq {r r' : LinkM WsForkOut} (hk : Over.K r) (h : fromEq OutAlike r r') :
    RunFree (some <$> r) (some <$> r') := by
  rw [← bind_pure_comp, ← bind_pure_comp]
  intro C F
  exact relB_mono (fun _ _ k => ⟨k.1.1, k.1.2, fun X l => samePlan_alike k.2 X l⟩)
    (fromEq_then (R := OptAlike) hk h
      (fun a a' k => cmpLA.pure' (R := OptAlike) (a := some a) (a' := some a') k) C F)

/-- A step of a computation that can refuse. -/
private theorem ok_bind2 {ε α β : Type} {x : Except ε α} {f : α → Except ε β} {b : β}
    (h : (x >>= f) = .ok b) : ∃ a, x = .ok a ∧ f a = .ok b := by
  cases x with
  | error e =>
    have h' : (Except.error e : Except ε β) = .ok b := h
    cases h'
  | ok a => exact ⟨a, rfl, h⟩

/-- What `coveredOf` returns has four arrays of T entries. -/
theorem covered_sizes {so : StOwn} {T V : Nat} {cov : Covered} (h : coveredOf so T V = .ok cov) :
    cov.tokv.size = T ∧ cov.hOn.size = T ∧ cov.hWin.size = T ∧ cov.hOnC.size = T := by
  refine ⟨(covered_tokens h).1, ?_⟩
  unfold coveredOf at h
  obtain ⟨_, -, h⟩ := ok_bind2 h
  obtain ⟨_, -, h⟩ := ok_bind2 h
  dsimp only at h
  obtain ⟨_, -, h⟩ := ok_bind2 h
  obtain ⟨_, -, h⟩ := ok_bind2 h
  cases h
  simp only [Array.size_map, Array.size_range, and_self]

/-- **The check of the head at two requests**, from the seven pieces. -/
theorem headFree_of (h1 : HearFree) (h2 : TablesFree) (h3 : TranscriptFree)
    (h4 : WeightsClaimFree) (h5 : WalkFree) (h6 : SelfTestsFree) (h7 : DoorFree)
    (p : Verify.Planned) : HeadFree p := by
  intro so so' cov cov' hc hc'
  have s := covered_sizes hc
  have s' := covered_sizes hc'
  exact runFree_of_fromEq (by keeps) (runForkHidH2_rel h1 h2 h3 h4 h5 h6 h7 _ _ _ _ _
    ⟨s.1.trans s'.1.symm, s.2.1.trans s'.2.1.symm, s.2.2.1.trans s'.2.2.1.symm,
      s.2.2.2.trans s'.2.2.2.symm⟩ _)

end OnBytes.Flat
