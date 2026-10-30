-- Copyright 2026 Anthropic PBC
-- SPDX-License-Identifier: Apache-2.0
--
/-
Johnson/Road/K4/K4Decls.lean: the reads that the layers' own rounds (K4) declare at a layers' link,
in the record of a declared read (ReadDecl, Johnson/Desc/Reads/Decl.lean), and THE EQUATION: the
list of tables that a hearing of K4's text returns (o.funs) is the list to which these declarations
unfold: no table more, none less, in this order, with the declared weights BY MAKE (FunsAre,
Johnson/Desc/Reads/DeclRow.lean).

The declarations are made from what K4's text asks for, not from the list: from the families of
tables (tableAsks, OnBytes/Model/LayerForms.lean), the rows and columns of the link's matrices, and
the weights' formula at the heard points (phiOf, OnBytes/Model/Layer.lean). A family's first entry
is the sum of the lengths of the families in front. No field is read off o.funs. BUT tableAsks,
layParts (which gives the running first entry) and phiOf ARE THE VERY ROUTINES BY WHICH THE HEARING
MAKES o.funs: so the equation is the unrolling of one list on both sides; what stands between the
two is layParts_eq and the order of a flatten. The weights w are the reader of phiOf's
array: no formula in a point's letters is stated. The one field that is written here by hand is
make.

  `makeOf y a`: how an entry's cells are counted off: a long family: blocks of L / T features; a
    family on the matrix of the lookup's planes: whole columns; else: short.
  `k4Decl y mats a p phi`: the declaration of the family a, laid from entry p on.
  `k4Decls y fo pt mats asks p`: those of a list of families, one behind the other.
  `pairOf`, `fam_tables`, `k4_tables`: steps: table for table the four numbers and the reader of
    the weights are those to which the declarations unfold.
  `k4_funsAre`: the equation, from the returns of layTables, funsOf and k4Decls.
  `k4Decls_some`: where funsOf returns, k4Decls does.
  `k4_funsAre_hear`: the equation at a hearing: at o.funs.
Limits. PREMISES OF THE EQUATION: the sizes t have the rows and columns of the list mats; each part
of a family has the rows and columns of its first part; every table's array of weights is as long
as its run (hsz: the row's own test on lengths, lensB: not shown here of phiOf). NOT HERE: Whole,
PartsFit, the join, the address of a use: that a form of K4's names the entry that its clause means.
The three families on the lookup's planes are declared here too, since K4's hearing lays them: a
table with two readers is one declaration; that the lookup's own declaration of them is this one
has not been held: its text is not with us. Met through Lean at no member. Nothing on soundness.


-/
import Johnson.Desc.Reads.DeclRow
import Johnson.Road.FormsKeysTab
import OnBytes.Tie.Pv.Tail.ShapesLay
import OnBytes.Desc.First.K4.HearPublic

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace OnBytes.Road.K4

open OnBytes OnBytes.Model OnBytes.K.Kc
open OnBytes.Model.Layer (Lay TableAsk TableAt layParts layTables tableAsks phiOf funsOf Pub Own
  HPlan2 pointsOf matIx)
open OnBytes.Tie.Pv.Tail.Closed (famFuns)
open OnBytes.Desc.First.K4 (engFl hear)
open VerifiableInference.Reads
open Cb.Pv.Tail (TSize)

/-- How an entry's cells are counted off in a family of tables. -/
def makeOf (y : Lay) (a : TableAsk) : Make :=
  if a.lng then .long (a.L / y.T) else if a.M0 == (matIx y).iB then .column else .short

/-- The declaration of one family of tables, laid from entry p on. mats: the rows and the columns of
each matrix of the link's list. phi: the family's weights. -/
def k4Decl (y : Lay) (mats : Array (ℕ × ℕ)) (a : TableAsk) (p : ℕ) (phi : Array E) : ReadDecl E :=
  { name := a.name, mat := a.M0, parts := a.parts, make := makeOf y a, len := a.L,
    count := a.parts * ((mats.getD a.M0 (0, 0)).2 * ((mats.getD a.M0 (0, 0)).1 / a.L)),
    start := p, w := fun j => phi.getD j zeroE }

/-- The declarations of a list of families, one behind the other from entry p on. -/
def k4Decls (y : Lay) (fo : Forest.Heard) (pt : List (String × Array E)) (mats : Array (ℕ × ℕ)) :
    List TableAsk → ℕ → Option (List (ReadDecl E))
  | [], _ => some []
  | a :: rest, p =>
    (phiOf y fo pt a).bind fun phi =>
      (k4Decls y fo pt mats rest (layParts mats a a.parts p).2).map fun ds =>
        k4Decl y mats a p phi :: ds

/-- A table's four numbers, and the reader of its weights. -/
def pairOf (Fn : HFun) : VerifiableInference.Reads.Laid × (ℕ → E) :=
  (laidOf Fn, fun j => Fn.phi.getD j zeroE)

/-- One family. -/
theorem fam_tables {y : Lay} {fo : Forest.Heard} {pt : List (String × Array E)}
    {mats : Array (ℕ × ℕ)} (t : TSize) (ht : ∀ i, mats.getD i (0, 0) = (t.m i, t.k i))
    (a : TableAsk) (p : ℕ)
    (hf : ∀ q, q < a.parts → mats.getD (a.M0 + q) (0, 0) = mats.getD a.M0 (0, 0))
    {b : List HFun} {phi : Array E} (hp : phiOf y fo pt a = some phi)
    (hb : famFuns y fo pt (a, (layParts mats a a.parts p).1) = some b) :
    b.map pairOf = tablesOf t [k4Decl y mats a p phi] := by
  unfold famFuns at hb
  rw [hp] at hb
  obtain rfl := Option.some.inj hb
  rw [layParts_eq mats a (t.m a.M0) (t.k a.M0) (fun q hq => (hf q hq).trans (ht a.M0)) p]
  unfold tablesOf
  rw [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  unfold ReadDecl.tabs
  rw [List.map_map, List.map_map, List.map_map]
  rfl

/-- All families. -/
theorem k4_tables {y : Lay} {fo : Forest.Heard} {pt : List (String × Array E)}
    {mats : Array (ℕ × ℕ)} (t : TSize) (ht : ∀ i, mats.getD i (0, 0) = (t.m i, t.k i)) :
    ∀ (asks : List TableAsk) (p : ℕ) (r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ)
      (l : List (List HFun)) (ds : List (ReadDecl E)),
      (∀ a ∈ asks, ∀ q, q < a.parts → mats.getD (a.M0 + q) (0, 0) = mats.getD a.M0 (0, 0)) →
      layTables mats asks p = some r → r.2.1.mapM (famFuns y fo pt) = some l →
      k4Decls y fo pt mats asks p = some ds → l.flatten.map pairOf = tablesOf t ds
  | [], p, r, l, ds, _, h, hl, hd => by
    have e : r = ([], [], p) := by simpa [layTables] using h.symm
    subst e
    rw [List.mapM_nil] at hl
    obtain rfl := Option.some.inj hl
    obtain rfl := Option.some.inj hd
    rfl
  | a :: rest, p, r, l, ds, hf, h, hl, hd => by
    have h' : (if ((layParts mats a a.parts p).2 == p) = true then none else
        (layTables mats rest (layParts mats a a.parts p).2).map fun r =>
          ((⟨a.name, p, (layParts mats a a.parts p).2 - p⟩ : TableAt) :: r.1,
            (a, (layParts mats a a.parts p).1) :: r.2.1, r.2.2)) = some r := h
    by_cases hq : ((layParts mats a a.parts p).2 == p) = true
    · rw [if_pos hq] at h'
      cases h'
    · rw [if_neg hq] at h'
      obtain ⟨r', h1, h2⟩ := map_some h'
      subst h2
      have hl' : ((a, (layParts mats a a.parts p).1) :: r'.2.1).mapM (famFuns y fo pt) = some l :=
        hl
      rw [List.mapM_cons] at hl'
      obtain ⟨b, hb, hl2⟩ := bind_some hl'
      obtain ⟨bs, hbs, hl3⟩ := bind_some hl2
      obtain rfl := Option.some.inj hl3
      have hd' : ((phiOf y fo pt a).bind fun phi =>
          (k4Decls y fo pt mats rest (layParts mats a a.parts p).2).map fun ds =>
            k4Decl y mats a p phi :: ds) = some ds := hd
      obtain ⟨phi, hp, hd2⟩ := Option.bind_eq_some_iff.mp hd'
      obtain ⟨ds', hd3, rfl⟩ := map_some hd2
      have i1 := k4_tables t ht rest _ r' bs ds'
        (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha')) h1 hbs hd3
      have j1 := fam_tables t ht a p (hf a List.mem_cons_self) hp hb
      rw [List.flatten_cons, List.map_append, i1, j1]
      unfold tablesOf
      rw [List.flatMap_cons, List.flatMap_cons, List.flatMap_nil, List.append_nil]

/-- **The equation**, from the three returns. -/
theorem k4_funsAre {y : Lay} {fo : Forest.Heard} {pt : List (String × Array E)}
    {mats : Array (ℕ × ℕ)} (t : TSize) (ht : ∀ i, mats.getD i (0, 0) = (t.m i, t.k i))
    {asks : List TableAsk} {p : ℕ} {r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ}
    {funs : Array HFun} {ds : List (ReadDecl E)}
    (hf : ∀ a ∈ asks, ∀ q, q < a.parts → mats.getD (a.M0 + q) (0, 0) = mats.getD a.M0 (0, 0))
    (h : layTables mats asks p = some r) (hfu : funsOf y fo pt r.2.1 = some funs)
    (hd : k4Decls y fo pt mats asks p = some ds)
    (hsz : ∀ Fn ∈ funs.toList, Fn.phi.size = Fn.len) : FunsAre t funs ds := by
  have h' : (r.2.1.mapM (famFuns y fo pt) >>= fun l => pure l.flatten.toArray) = some funs := hfu
  obtain ⟨l, hl, h2⟩ := bind_some h'
  obtain rfl := Option.some.inj h2
  have e := k4_tables t ht asks p r l ds hf h hl hd
  have e' : l.flatten.toArray.toList.map pairOf = tablesOf t ds := e
  refine ⟨?_, fun n Fn x hn hx => ⟨hsz Fn (List.mem_of_getElem? hn), fun j _ => ?_⟩⟩
  · rw [← e', List.map_map]
    rfl
  · rw [← e', List.getElem?_map, hn] at hx
    obtain rfl := Option.some.inj hx
    rfl

/-- Where funsOf returns on what layTables has laid, the declarations are there. -/
theorem k4Decls_some {y : Lay} {fo : Forest.Heard} {pt : List (String × Array E)}
    {mats : Array (ℕ × ℕ)} :
    ∀ (asks : List TableAsk) (p : ℕ) (r : List TableAt × List (TableAsk × List (ℕ × ℕ)) × ℕ)
      (l : List (List HFun)), layTables mats asks p = some r →
      r.2.1.mapM (famFuns y fo pt) = some l → ∃ ds, k4Decls y fo pt mats asks p = some ds
  | [], _, _, _, _, _ => ⟨[], rfl⟩
  | a :: rest, p, r, l, h, hl => by
    have h' : (if ((layParts mats a a.parts p).2 == p) = true then none else
        (layTables mats rest (layParts mats a a.parts p).2).map fun r =>
          ((⟨a.name, p, (layParts mats a a.parts p).2 - p⟩ : TableAt) :: r.1,
            (a, (layParts mats a a.parts p).1) :: r.2.1, r.2.2)) = some r := h
    by_cases hq : ((layParts mats a a.parts p).2 == p) = true
    · rw [if_pos hq] at h'
      cases h'
    · rw [if_neg hq] at h'
      obtain ⟨r', h1, h2⟩ := map_some h'
      subst h2
      have hl' : ((a, (layParts mats a a.parts p).1) :: r'.2.1).mapM (famFuns y fo pt) = some l :=
        hl
      rw [List.mapM_cons] at hl'
      obtain ⟨b, hb, hl2⟩ := bind_some hl'
      obtain ⟨bs, hbs, _⟩ := bind_some hl2
      obtain ⟨ds', hd'⟩ := k4Decls_some rest _ r' bs h1 hbs
      unfold famFuns at hb
      obtain ⟨phi, hp, _⟩ := bind_some hb
      have hp' : phiOf y fo pt a = some phi := hp
      refine ⟨k4Decl y mats a p phi :: ds', ?_⟩
      show ((phiOf y fo pt a).bind fun phi =>
          (k4Decls y fo pt mats rest (layParts mats a a.parts p).2).map fun ds =>
            k4Decl y mats a p phi :: ds) = _
      rw [hp', Option.bind_some, hd', Option.map_some]

/-- **The equation at a hearing.** -/
theorem k4_funsAre_hear {P : Pub} {hp : HPlan2} {g : ℕ} {fo : Forest.Heard} {F G : Fork}
    {t u : Tape} {o : Own} (h : hear engFl P hp g fo F t = some (o, G, u)) (tz : TSize)
    (ht : ∀ i, ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)).getD i (0, 0) =
      (tz.m i, tz.k i))
    (hf : ∀ a ∈ tableAsks P.y P.rd g, ∀ q, q < a.parts →
      ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)).getD (a.M0 + q) (0, 0) =
        ((P.tails.getD g {}).mats.map fun M => (M.m, M.k)).getD a.M0 (0, 0))
    (hsz : ∀ Fn ∈ o.funs.toList, Fn.phi.size = Fn.len) :
    ∃ pts ds, pointsOf P.y o.H o.hd o.hd2 = some pts ∧
      k4Decls P.y fo pts ((P.tails.getD g {}).mats.map fun M => (M.m, M.k))
        (tableAsks P.y P.rd g) 0 = some ds ∧ FunsAre tz o.funs ds := by
  obtain ⟨_, _, iU3, tab, laid, nU3, TS, claimsP, pts, hd2, _, _, e3, _, _, _, _, e8, e9, e10⟩ :=
    Desc.First.K4.hear_public h
  have h' : (laid.mapM (famFuns P.y fo pts) >>= fun l => pure l.flatten.toArray) = some o.funs :=
    e10
  obtain ⟨l, hl, _⟩ := bind_some h'
  obtain ⟨ds, hd⟩ := k4Decls_some _ 0 (tab, laid, nU3) l e3 hl
  exact ⟨pts, ds, by rw [e8]; exact e9, hd, k4_funsAre tz ht hf e3 e10 hd hsz⟩

end OnBytes.Road.K4

#print axioms OnBytes.Road.K4.k4_funsAre_hear
#print axioms OnBytes.Road.K4.fam_tables
#print axioms OnBytes.Road.K4.k4_tables
#print axioms OnBytes.Road.K4.k4_funsAre
#print axioms OnBytes.Road.K4.k4Decls_some
