-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
/-
OnBytes/Tie/Pv/Lookup/Ends/FoAttLists1.lean.
Which claims the check of the attention sub-proof adds, as written lists: the readers, and claims 3
and 4.

The routines of OnBytes/Model/AttentionClaimsA.lean make their forms by readers that end in `uEnt`
(OnBytes/Model/Look.lean), which asks the state for the number of columns of the array of tables. So
the list of the claims that such a routine adds is a function of the heard record h and of that one
number K. The rules are those of OnBytes/Tie/Pv/Lookup/Ends/FoRd.lean: `Rd t K r v`: from a state in
which array t has K columns the routine r, if it returns, leaves the state and returns v. `AdV t K r
v l` and `Ad t K r l`: from such a state with one coefficient for each slot r, if it returns,
returns v and ends in such a state, which comes from the first by adding just the list l.

Main names:
 * `rd_u3at`, `rd_weighted`, `rd_lessPieces`, `rd_plane`, `rd_shV`, `rd_readMaximum`, `rd_xl`,
   `rd_readHead`, `rd_readGroup`: the readers' values. The written forms `planeF`, `shVF`,
   `readMaximumF`, `xlF` stand in OnBytes/Tie/Pv/Lookup/Ends/FoClaim3Members.lean and
   OnBytes/Tie/Pv/Lookup/Ends/FoReadersWritten.lean; `xlT`, `readHeadT`, `readGroupT` are total
   forms made of them.
 * `linPlanesT`, `callKRT`, `claim3T`, with the values `callKRV`, `claim3V`; `ad_linPlanes`,
   `adV_callKR`, `adV_claim3`: claim 3.
 * `endValuesT`, `unitKFDT`, `callKFDT`, `claim4T`, with the values `callKFDV`, `claim4V`;
   `ad_endValues`, `ad_unitKFD`, `adV_callKFD`, `adV_claim4`: claim 4.

What is lost against the routines: the values and the lists here are total. They do not say where a
routine refuses: `xlT` is the empty form where `xl` refuses, and `unitKFDT` is empty where `unitKFD`
does. Off a run that returns, a list means nothing. Nothing says that a routine returns. The lists
are tied to a run by `Adds` (OnBytes/Tie/Pv/Led/LedAdds.lean): the forms are added one after the
other, in the list's order; `Added` (OnBytes/Tie/Pv/Lookup/Ends/FoAdded.lean) is not concluded here.
What the forms are worth is not said.

Not claimed: anything on soundness, completeness or hiding.

-/
import OnBytes.Tie.Pv.Lookup.Ends.FoRd
import OnBytes.Tie.Pv.Lookup.Ends.FoReadersWritten

set_option autoImplicit false

namespace Fo
open OnBytes OnBytes.Model OnBytes.PscRun OnBytes.Attention

variable {K : ℕ}

/-- `u3at`, if it returns, leaves the state and returns the form of the entry. -/
theorem rd_u3at (h : Attention.Heard) (t i : ℕ) :
    Rd h.iU3 K (u3at h t i) (u3Form h.iU3 K (t + i)) :=
  Rd.bind (Rd.unit _) (rd_uEnt _ _)

/-- `weighted`, if it returns, leaves the state and returns `weightedF`, where each of its readers,
if it returns, leaves the state and returns a written form. -/
theorem rd_weighted {t : ℕ} (n : ℕ) (w : Array E) (f : ℕ → SubM Aff) (fv : ℕ → Aff)
    (hf : ∀ i, Rd t K (f i) (fv i)) : Rd t K (weighted n w f) (weightedF n w fv) :=
  Rd.foldlM (fun s i => do
      let x ← f i
      pure (Aff.addMul s x (w.getD i zeroE)))
    (fun s i => Aff.addMul s (fv i) (w.getD i zeroE))
    (fun _ i => Rd.bind (hf i) (Rd.pure _)) _ _

/-- `lessPieces`, if it returns, leaves the state and returns `lessF`, likewise. -/
theorem rd_lessPieces {t : ℕ} (start : Aff) (pw : Array PW) (f : PW → SubM Aff) (fv : PW → Aff)
    (hf : ∀ w, Rd t K (f w) (fv w)) : Rd t K (lessPieces start pw f) (lessF start pw fv) := by
  unfold lessPieces lessF
  rw [← Array.foldlM_toList]
  exact Rd.foldlM (fun s w => do
      let x ← f w
      pure (Aff.addMul s x (mulE minusOne w.wp)))
    (fun s w => Aff.addMul s (fv w) (mulE minusOne w.wp))
    (fun _ w => Rd.bind (hf w) (Rd.pure _)) _ _

/-- `plane`, if it returns, leaves the state and returns `planeF`. -/
theorem rd_plane (h : Attention.Heard) (t x lam a : ℕ) (z : Array E) (isD : Bool) :
    Rd h.iU3 K (plane h t x lam a z isD) (planeF h K t x lam a z isD) :=
  rd_weighted _ _ _ _ fun _ => rd_u3at h t _

/-- `shV`, if it returns, leaves the state and returns `shVF`. -/
theorem rd_shV (h : Attention.Heard) (t off nl J lam j : ℕ) :
    Rd h.iU3 K (shV h t off nl J lam j) (shVF h K t off nl J lam j) :=
  rd_weighted _ _ _ _ fun _ => rd_u3at h t _

/-- `readMaximum`, if it returns, leaves the state and returns `readMaximumF`. -/
theorem rd_readMaximum (h : Attention.Heard) (t : ℕ) (zg : Array E) (lam a : ℕ) :
    Rd h.iU3 K (readMaximum h t zg lam a) (readMaximumF h K t zg lam a) :=
  rd_weighted _ _ _ _ fun _ => rd_shV h t _ _ _ _ _

/-! ### claim 3 -/

/-- The claims of `linPlanes`: one for each plane of the plane claim. -/
def linPlanesT (h : Attention.Heard) (K : ℕ) (pc : PlaneClaim) : List Aff :=
  (List.range pc.np).flatMap fun x =>
    [lessF (Aff.slot (pc.s0 + x)) pc.pw fun w => planeF h K h.t.tA x w.lam w.a pc.z pc.isD]

/-- `linPlanes`, if it returns, has added them. -/
theorem ad_linPlanes (h : Attention.Heard) (pc : PlaneClaim) :
    Ad h.iU3 K (linPlanes h pc) (linPlanesT h K pc) :=
  Ad.forM _ _ (fun _ => Ad.after (rd_lessPieces _ _ _ _ fun _ => rd_plane h _ _ _ _ _ _)
    (Ad.lin _)) _

/-- The key form that `callKR` returns. -/
def callKRV (h : Attention.Heard) (q : ℕ) : Aff :=
  h.planes.toList.foldl (fun v pc => if pc.call == q then v + keyKR pc else v) (Aff.ofConst zeroE)

/-- The claims of `callKR`: those of the call's units, in the order of the plane claims. -/
def callKRT (h : Attention.Heard) (K q : ℕ) : List Aff :=
  h.planes.toList.flatMap fun pc => if pc.call == q then linPlanesT h K pc ++ [] else []

/-- `callKR`, if it returns, returns the one and has added the other. -/
theorem adV_callKR (h : Attention.Heard) (q : ℕ) :
    AdV h.iU3 K (callKR h q) (callKRV h q) (callKRT h K q) := by
  unfold callKR
  rw [← Array.foldlM_toList]
  exact AdV.foldlM
    (fun v pc => if pc.call == q then do
        linPlanes h pc
        pure (v + keyKR pc)
      else pure v)
    (fun v pc => if pc.call == q then v + keyKR pc else v)
    (fun pc => if pc.call == q then linPlanesT h K pc ++ [] else [])
    (fun _ pc => AdV.ite (AdV.seq (ad_linPlanes h pc) (AdV.pure _)) (AdV.pure _)) _ _

/-- The joins that claim 3 returns. -/
def claim3V (h : Attention.Heard) (j : Joins) : Joins :=
  h.S.calls.toList.zipIdx.foldl
    (fun j x => if x.1.kind == .kr then j.set x.2 (callKRV h x.2) else j) j

/-- The claims of claim 3. -/
def claim3T (h : Attention.Heard) (K : ℕ) : List Aff :=
  h.S.calls.toList.zipIdx.flatMap fun x =>
    if x.1.kind == .kr then callKRT h K x.2 ++ [] else []

/-- **Claim 3, if it returns, returns the written joins and has added the written list.** -/
theorem adV_claim3 (h : Attention.Heard) (j : Joins) :
    AdV h.iU3 K (claim3 h j) (claim3V h j) (claim3T h K) :=
  AdV.foldlM
    (fun (j : Joins) (x : ACall × ℕ) => if x.1.kind == .kr then do
        let v ← callKR h x.2
        pure (j.set x.2 v)
      else pure j)
    (fun (j : Joins) (x : ACall × ℕ) => if x.1.kind == .kr then j.set x.2 (callKRV h x.2) else j)
    (fun (x : ACall × ℕ) => if x.1.kind == .kr then callKRT h K x.2 ++ [] else [])
    (fun _ x => AdV.ite (AdV.bind (adV_callKR h x.2) (AdV.pure _)) (AdV.pure _)) _ _

/-! ### xl, readHead, readGroup -/

/-- The form of xl, total: the empty form where xl refuses. -/
def xlT (h : Attention.Heard) (K t : ℕ) (X : TenAt) (lam hd : ℕ) (zc : Array E) : Aff :=
  (xlF h K t X lam hd zc).getD {}

/-- `xl`, if it returns, leaves the state and returns `xlT`. Where it refuses nothing is said. -/
theorem rd_xl (h : Attention.Heard) (t : ℕ) (X : TenAt) (lam hd : ℕ) (zc : Array E) :
    Rd h.iU3 K (xl h t X lam hd zc) (xlT h K t X lam hd zc) := by
  unfold xl xlT xlF
  dsimp only
  cases cutLast (zc.extract 0 h.S.cf.ldh) h.S.ls with
  | error e => exact Rd.never (refuse_never _) _
  | ok cut =>
    dsimp only
    cases headFeat X hd h.S.dh with
    | error e => exact Rd.never (refuse_never _) _
    | ok j0 =>
      exact rd_weighted _ _ _ _ fun _ => rd_weighted _ _ _ _ fun _ => rd_u3at h t _

/-- The form of `readHead`, total. -/
def readHeadT (h : Attention.Heard) (K t : ℕ) (X : TenAt) (zg zc : Array E) (lam a : ℕ) : Aff :=
  overGF h zg fun g => xlT h K t X lam (g * h.S.HA + a) zc

/-- `readHead`, if it returns, leaves the state and returns `readHeadT`. -/
theorem rd_readHead (h : Attention.Heard) (t : ℕ) (X : TenAt) (zg zc : Array E) (lam a : ℕ) :
    Rd h.iU3 K (readHead h t X zg zc lam a) (readHeadT h K t X zg zc lam a) :=
  rd_weighted _ _ _ _ fun _ => rd_xl h t X lam _ zc

/-- The form of `readGroup`, total. -/
def readGroupT (h : Attention.Heard) (K t : ℕ) (X : TenAt) (zg zc : Array E) (lam : ℕ) : Aff :=
  overGF h zg fun g => xlT h K t X lam g zc

/-- `readGroup`, if it returns, leaves the state and returns `readGroupT`. -/
theorem rd_readGroup (h : Attention.Heard) (t : ℕ) (X : TenAt) (zg zc : Array E) (lam : ℕ) :
    Rd h.iU3 K (readGroup h t X zg zc lam) (readGroupT h K t X zg zc lam) :=
  rd_weighted _ _ _ _ fun _ => rd_xl h t X lam _ zc

/-! ### claim 4 -/

/-- The two claims of `endValues`. -/
def endValuesT (h : Attention.Heard) (K : ℕ) (k : Score) (tb : ScoreTables) (rc : Array E)
    (b : ℕ) (w : PW) : List Aff :=
  [sc3A k.sc b - readHeadT h K tb.tQ h.S.atQ k.sc.r rc w.lam w.a] ++
    [sc3B k.sc b - readGroupT h K tb.tK h.S.atK k.sc.r rc w.lam]

/-- `endValues`, if it returns, has added them. -/
theorem ad_endValues (h : Attention.Heard) (k : Score) (tb : ScoreTables) (rc : Array E) (b : ℕ)
    (w : PW) : Ad h.iU3 K (endValues h k tb rc b w) (endValuesT h K k tb rc b w) :=
  Ad.after (rd_readHead h _ _ _ _ _ _) (Ad.seq (Ad.lin _)
    (Ad.after (rd_readGroup h _ _ _ _ _) (Ad.lin _)))

/-- The claims of `unitKFD`: the planes', the row maximum's, the row of the unit's sumcheck, the end
values'. Empty where the unit's tables or its plane claim are missing: there `unitKFD` refuses. -/
def unitKFDT (h : Attention.Heard) (K i : ℕ) (k : Score) : List Aff :=
  match h.t.score[i]?, h.planes[k.claim]? with
  | some tb, some pc =>
    linPlanesT h K pc ++
      ([lessF (Aff.slot (k.s0 + 5)) k.pw fun w => readMaximumF h K tb.tM k.zg w.lam w.a] ++
        ([k.sc.rowU] ++ k.pw.toList.zipIdx.flatMap fun x =>
          endValuesT h K k tb (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size) x.2 x.1))
  | _, _ => []

/-- `unitKFD`, if it returns, has added them. -/
theorem ad_unitKFD (h : Attention.Heard) (i : ℕ) (k : Score) :
    Ad h.iU3 K (unitKFD h i k) (unitKFDT h K i k) := by
  unfold unitKFD unitKFDT
  cases h.t.score[i]? with
  | none => exact AdV.ad (AdV.never (getNone_never _) _ _)
  | some tb =>
    refine Ad.after (rd_getSome tb) ?_
    cases h.planes[k.claim]? with
    | none => exact AdV.ad (AdV.never (getNone_never _) _ _)
    | some pc =>
      refine Ad.after (rd_getSome pc) (Ad.seq (ad_linPlanes h pc) ?_)
      refine Ad.after (rd_lessPieces (Aff.slot (k.s0 + 5)) k.pw
        (fun w => readMaximum h tb.tM k.zg w.lam w.a)
        (fun w => readMaximumF h K tb.tM k.zg w.lam w.a)
        fun w => rd_readMaximum h tb.tM k.zg w.lam w.a) ?_
      refine Ad.seq (Ad.lin _) (Ad.seq (Ad.lin _) ?_)
      exact Ad.forM
        (fun x : PW × ℕ => endValues h k tb
          (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size) x.2 x.1)
        (fun x => endValuesT h K k tb
          (k.sc.r.extract (k.sc.r.size - h.S.cf.ldh) k.sc.r.size) x.2 x.1)
        (fun x => ad_endValues h k tb _ x.2 x.1) _

/-- The key form that `callKFD` returns. -/
def callKFDV (h : Attention.Heard) (q : ℕ) (c : ACall) : Aff :=
  h.scores.toList.zipIdx.foldl
    (fun v x => if x.1.call == q then v + keyKFD (h.S.shd c.sh) x.1 else v)
    (padTerm c (h.g.zk.getD q #[]))

/-- The claims of `callKFD`: those of the call's units, in the order of the scores. -/
def callKFDT (h : Attention.Heard) (K q : ℕ) : List Aff :=
  h.scores.toList.zipIdx.flatMap fun x =>
    if x.1.call == q then unitKFDT h K x.2 x.1 ++ [] else []

/-- `callKFD`, if it returns, returns the one and has added the other. -/
theorem adV_callKFD (h : Attention.Heard) (q : ℕ) (c : ACall) :
    AdV h.iU3 K (callKFD h q c) (callKFDV h q c) (callKFDT h K q) :=
  AdV.foldlM
    (fun (v : Aff) (x : Score × ℕ) => if x.1.call == q then do
        unitKFD h x.2 x.1
        pure (v + keyKFD (h.S.shd c.sh) x.1)
      else pure v)
    (fun (v : Aff) (x : Score × ℕ) => if x.1.call == q then v + keyKFD (h.S.shd c.sh) x.1 else v)
    (fun (x : Score × ℕ) => if x.1.call == q then unitKFDT h K x.2 x.1 ++ [] else [])
    (fun _ x => AdV.ite (AdV.seq (ad_unitKFD h x.2 x.1) (AdV.pure _)) (AdV.pure _)) _ _

/-- The joins that claim 4 returns. -/
def claim4V (h : Attention.Heard) (j : Joins) : Joins :=
  h.S.calls.toList.zipIdx.foldl
    (fun j x => if x.1.kind == .kfd then j.set x.2 (callKFDV h x.2 x.1) else j) j

/-- The claims of claim 4. -/
def claim4T (h : Attention.Heard) (K : ℕ) : List Aff :=
  h.S.calls.toList.zipIdx.flatMap fun x =>
    if x.1.kind == .kfd then callKFDT h K x.2 ++ [] else []

/-- **Claim 4, if it returns, returns the written joins and has added the written list.** -/
theorem adV_claim4 (h : Attention.Heard) (j : Joins) :
    AdV h.iU3 K (claim4 h j) (claim4V h j) (claim4T h K) :=
  AdV.foldlM
    (fun (j : Joins) (x : ACall × ℕ) => if x.1.kind == .kfd then do
        let v ← callKFD h x.2 x.1
        pure (j.set x.2 v)
      else pure j)
    (fun (j : Joins) (x : ACall × ℕ) =>
      if x.1.kind == .kfd then j.set x.2 (callKFDV h x.2 x.1) else j)
    (fun (x : ACall × ℕ) => if x.1.kind == .kfd then callKFDT h K x.2 ++ [] else [])
    (fun _ x => AdV.ite (AdV.bind (adV_callKFD h x.2 x.1) (AdV.pure _)) (AdV.pure _)) _ _

end Fo
