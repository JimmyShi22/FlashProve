//! The plan of one protocol run and its verdict, ported from `blocks/numbers/plan.h`.
//!
//! S2a ports the data model and the verdict needed by the error accounting. The planners of
//! `blocks/numbers/blocks.h`, which append rounds from shapes, arrive with the proof-system shapes
//! in S2b. A `Planned` here is built from a C++ dump or, later, by the ported planners.

use alloc::collections::BTreeMap;
use alloc::string::String;
use alloc::vec::Vec;
use core::cmp::Ordering;

use super::real::{
    bits_of, Big, Bound, Dir, Real, DRAW_TRIES, NONZERO_TRIES,
};
use super::setting::{CountSource, ErrorKind, RoundKind, Scope, Setting};

/// What a round's error bound was computed from (`Priced`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Priced {
    Nothing,
    SettingAlone,
    TheRoundItself,
    AsSaid,
    OnTheCallersWord,
}

/// Why a plan does not hold (`Cause`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Cause {
    None,
    Refused,
    AboveTheTarget,
    Word,
    TwoDistances,
}

/// The kind of a planned message (`MessageKind`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum MessageKind {
    Scalars,
    Answers,
    Root,
    Nonce,
    Columns,
    Salts,
    Paths,
    Head,
}

/// Which test on the committed table a round belongs to (`TableTest`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum TableTest {
    Later,
    OneTime,
    Link,
}

/// The public numbers of one code in a group (`PricedCode`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct PricedCode {
    pub log_n: u32,
    pub ell: u64,
    pub r: u64,
}

/// A group's stated public numbers and analysis choice (`PricedGroup`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PricedGroup {
    pub main: PricedCode,
    pub mask: PricedCode,
    pub k: u32,
    pub h: u32,
    pub slots: u64,
    pub said: bool,
    pub rule: u32,
    pub m: u64,
}

impl Default for PricedGroup {
    fn default() -> Self {
        PricedGroup {
            main: PricedCode::default(),
            mask: PricedCode::default(),
            k: 0,
            h: 0,
            slots: 1,
            said: false,
            rule: 0,
            m: 0,
        }
    }
}

/// The committed table's distances (`TableDistances`).
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
pub struct TableDistances {
    pub radius: u64,
    pub later_radius: u64,
    pub m_once: u64,
    pub m_later: u64,
}

/// A committed table's stated numbers (`PricedTable`).
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct PricedTable {
    pub code: PricedCode,
    pub v: u32,
    pub answers: u32,
    pub distances: TableDistances,
    pub said: bool,
    pub test: TableTest,
}

impl Default for PricedTable {
    fn default() -> Self {
        PricedTable {
            code: PricedCode::default(),
            v: 0,
            answers: 0,
            distances: TableDistances::default(),
            said: false,
            test: TableTest::Later,
        }
    }
}

/// One round (`PlanRound`).
#[derive(Clone, Debug)]
pub struct PlanRound {
    pub name: String,
    pub where_: String,
    pub kind: RoundKind,
    pub why: ErrorKind,
    pub scope: Scope,
    pub error: Real,
    pub rests: CountSource,
    pub work_bits: u32,
    pub count: u64,
    pub part: u32,
    pub message_bytes: usize,
    pub roots: u32,
    pub answers: u32,
    pub draw_e: u64,
    pub draw_nonzero: u64,
    pub draw_positions: u64,
    pub log_n: u32,
    pub draw_trits: u64,
    pub rows: u64,
    pub first_list: u64,
    pub group: PricedGroup,
    pub table: PricedTable,
    pub combinations: u64,
    pub sharing: u64,
    pub priced: Priced,
}

impl Default for PlanRound {
    fn default() -> Self {
        PlanRound {
            name: String::new(),
            where_: String::new(),
            kind: RoundKind::Empty,
            why: ErrorKind::Zero,
            scope: Scope::Request,
            error: Real::default(),
            rests: CountSource::Johnson,
            work_bits: 0,
            count: 1,
            part: 0,
            message_bytes: 0,
            roots: 0,
            answers: 0,
            draw_e: 0,
            draw_nonzero: 0,
            draw_positions: 0,
            log_n: 0,
            draw_trits: 0,
            rows: 0,
            first_list: 0,
            group: PricedGroup::default(),
            table: PricedTable::default(),
            combinations: 0,
            sharing: 0,
            priced: Priced::Nothing,
        }
    }
}

impl PlanRound {
    pub fn says(&self) -> bool {
        self.rows != 0
            || self.first_list != 0
            || self.group.said
            || self.table.said
            || self.combinations != 0
            || self.sharing != 0
    }

    /// Null, or how `priced` contradicts the rest of the round (`word_fault`).
    pub fn word_fault(&self) -> Option<&'static str> {
        if (self.draw_positions != 0 || self.draw_trits != 0)
            && self.error.zero()
            && self.priced != Priced::OnTheCallersWord
        {
            return Some("a round that draws positions or a matrix is priced at 0, which only a round marked ON_THE_CALLERS_WORD may be");
        }
        if self.priced == Priced::Nothing && !self.error.zero() {
            return Some("a round with an error is said to be priced from nothing");
        }
        if (self.priced == Priced::SettingAlone || self.priced == Priced::TheRoundItself)
            && self.says()
        {
            return Some("a round that is priced from the setting or from its own fields says something beside them");
        }
        if self.priced == Priced::AsSaid && !self.says() {
            return Some("a round that is priced from what the plan says beside it says nothing");
        }
        None
    }
}

/// The most 64-bit words of the chain's answer (`most_words`).
pub fn most_words(r: &PlanRound, degree: u32) -> u64 {
    DRAW_TRIES as u64
        * degree as u64
        * (r.draw_e + (NONZERO_TRIES as u64 - 1) * r.draw_nonzero)
        + r.draw_positions
        + (r.draw_trits + 31) / 32
        + if r.kind == RoundKind::Seal { 4 } else { 0 }
}

/// One run of bytes in a planned file (`PlanMessage`).
#[derive(Clone, Debug)]
pub struct PlanMessage {
    pub name: String,
    pub where_: String,
    pub kind: MessageKind,
    pub bytes: u64,
    pub expected: f64,
    pub count: u64,
    pub part: u32,
    pub in_chain: bool,
    pub hash_calls: u64,
}

impl Default for PlanMessage {
    fn default() -> Self {
        PlanMessage {
            name: String::new(),
            where_: String::new(),
            kind: MessageKind::Scalars,
            bytes: 0,
            expected: 0.0,
            count: 1,
            part: 0,
            in_chain: false,
            hash_calls: 0,
        }
    }
}

/// A finished plan and its verdict (`Planned`).
#[derive(Clone, Debug)]
pub struct Planned {
    pub set: Setting,
    pub rounds: Vec<PlanRound>,
    pub messages: Vec<PlanMessage>,
    pub parts: Vec<String>,
    pub cause: Cause,
    pub why_not: String,
}

impl Default for Planned {
    fn default() -> Self {
        Planned {
            set: Setting::default(),
            rounds: Vec::new(),
            messages: Vec::new(),
            parts: Vec::new(),
            cause: Cause::Refused,
            why_not: String::from("nothing was planned"),
        }
    }
}

impl Planned {
    pub fn new(
        set: Setting,
        rounds: Vec<PlanRound>,
        messages: Vec<PlanMessage>,
        parts: Vec<String>,
        refused: String,
    ) -> Self {
        let mut p = Planned {
            set,
            rounds,
            messages,
            parts,
            cause: Cause::None,
            why_not: String::new(),
        };
        let (cause, why) = p.judged(&refused);
        p.cause = cause;
        p.why_not = why;
        p
    }

    pub fn holds(&self) -> bool {
        self.cause == Cause::None
    }
    pub fn refused(&self) -> bool {
        self.cause == Cause::Refused
    }
    pub fn cause(&self) -> Cause {
        self.cause
    }
    pub fn why_not(&self) -> &str {
        &self.why_not
    }
    pub fn rounds_sum(&self) -> u64 {
        self.rounds.iter().map(|r| r.count).sum()
    }
    pub fn queries(&self) -> u64 {
        self.rounds_sum()
    }
    pub fn size_of(&self, part: u32) -> (u64, f64) {
        let mut bytes = 0u64;
        let mut expected = 0.0f64;
        for m in &self.messages {
            if m.part == part {
                bytes += m.bytes * m.count;
                expected += m.expected * m.count as f64;
            }
        }
        (bytes, expected)
    }
    pub fn part_index(&self, name: &str) -> Option<usize> {
        self.parts.iter().position(|p| p == name)
    }

    /// An upper bound on the chance that a draw of one E element reaches its cap (`capped`).
    pub fn capped(&self) -> Real {
        let mut bits = 0usize;
        while Big::cmp(&Big::two_to(bits), &self.set.p) == Ordering::Less {
            bits += 1;
        }
        let num = Big::sub(&Big::two_to(bits), &self.set.p);
        let den = Big::two_to(bits);
        let ratio = Bound::ratio(&num, &den);
        (Bound::from_u64(self.set.degree as u64) * Bound::pow(&ratio, DRAW_TRIES as u64))
            .error()
    }

    /// The round's error with the distance of its draws from uniform (`whole_error`).
    pub fn whole_error(&self, r: &PlanRound, unit: &Real) -> Real {
        if r.draw_e == 0 {
            return r.error.clone();
        }
        let n = Real::from_u64(r.draw_e + (NONZERO_TRIES as u64 - 1) * r.draw_nonzero);
        let mut e = Real::add(
            &r.error,
            &Real::mul(unit, &n, Dir::Up),
            Dir::Up,
        );
        if r.draw_nonzero != 0 {
            let card = self.set.card_e();
            let denom = Bound::pow(&Bound::from_big(&card), NONZERO_TRIES as u64);
            let term = (Bound::from_u64(1) / denom).error();
            e = Real::add(
                &e,
                &Real::mul(&term, &Real::from_u64(r.draw_nonzero), Dir::Up),
                Dir::Up,
            );
        }
        e
    }

    /// Does the round hold at the target, work counted? (`holds`).
    pub fn holds_round(&self, r: &PlanRound, unit: &Real) -> bool {
        let goal = Real::two_to(r.work_bits as i64 - self.set.target as i64);
        Real::cmp(&self.whole_error(r, unit), &goal) != Ordering::Greater
    }

    pub fn holds_round_default(&self, r: &PlanRound) -> bool {
        let unit = self.capped();
        self.holds_round(r, &unit)
    }

    fn at(i: usize, r: &PlanRound) -> String {
        alloc::format!(
            "round {}, {}{}: ",
            i + 1,
            r.name,
            if r.where_.is_empty() {
                String::new()
            } else {
                alloc::format!(", {}", r.where_)
            }
        )
    }

    fn judged(&self, refused: &str) -> (Cause, String) {
        if !refused.is_empty() {
            return (Cause::Refused, String::from(refused));
        }
        let unit = self.capped();
        for (i, r) in self.rounds.iter().enumerate() {
            if !self.holds_round(r, &unit) {
                return (
                    Cause::AboveTheTarget,
                    Self::at(i, r) + "the error is above the target, work counted",
                );
            }
            if let Some(fault) = r.word_fault() {
                return (Cause::Word, Self::at(i, r) + fault);
            }
        }
        let mut chosen: BTreeMap<[u64; 6], (u32, u64)> = BTreeMap::new();
        for (i, r) in self.rounds.iter().enumerate() {
            let g = &r.group;
            if !g.said {
                continue;
            }
            let key = [
                g.main.log_n as u64,
                g.main.ell,
                g.main.r,
                g.mask.log_n as u64,
                g.mask.ell,
                g.mask.r,
            ];
            let choice = (g.rule, g.m);
            if let Some(old) = chosen.get(&key) {
                if *old != choice {
                    return (
                        Cause::TwoDistances,
                        Self::at(i, r)
                            + "priced at another distance than an earlier round on the same two codes",
                    );
                }
            } else {
                chosen.insert(key, choice);
            }
        }
        (Cause::None, String::new())
    }
}

/// A part's size in bytes and on average (`PartSize`).
#[derive(Clone, Copy, Debug, Default)]
pub struct PartSize {
    pub bytes: u64,
    pub expected: f64,
}

/// Keep the accounting's digit-collapsing rule visible to tests.
pub fn round_bits(r: &PlanRound, p: &Planned) -> f64 {
    let unit = p.capped();
    bits_of(&p.whole_error(r, &unit))
}
