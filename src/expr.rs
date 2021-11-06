use std::{
    fmt::{self, Debug, Display},
    iter,
    ops::RangeInclusive,
};

use chrono::{Date, Datelike, NaiveDateTime, Timelike, Utc, Weekday};

type FieldIter = Box<dyn Iterator<Item = (bool, u8)>>;

const WEEKDAY_SUN: u8 = 1;
const WEEKDAY_MON: u8 = 2;
const WEEKDAY_TUE: u8 = 3;
const WEEKDAY_WED: u8 = 4;
const WEEKDAY_THU: u8 = 5;
const WEEKDAY_FRI: u8 = 6;
const WEEKDAY_SAT: u8 = 7;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum CronNormal {
    Val(u8),
    Range(RangeInclusive<u8>, u8),
    Enums(Box<[u8]>),
}

impl Display for CronNormal {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CronNormal::Val(x) => write!(f, "{}", x),
            CronNormal::Range(range, step) => {
                if *step == 1 {
                    write!(f, "{}-{}", range.start(), range.end())
                } else {
                    write!(f, "{}/{}", range.start(), step)
                }
            }
            CronNormal::Enums(enums) => {
                for i in enums.as_ref() {
                    write!(f, "{}", i)?;
                }
                Ok(())
            }
        }
    }
}

impl CronNormal {
    fn new_within_range(&self, range: RangeInclusive<u8>) -> Self {
        match self.clone() {
            CronNormal::Val(x) if range.contains(&x) => CronNormal::Val(x),
            #[allow(clippy::reversed_empty_ranges)]
            CronNormal::Val(_) => CronNormal::Range(1..=0, 1),
            CronNormal::Range(old_range, step) => CronNormal::Range(
                *old_range.start().min(range.start())..=*old_range.end().min(range.end()),
                step,
            ),
            CronNormal::Enums(enums) => CronNormal::Enums(
                enums
                    .iter()
                    .copied()
                    .filter(|x| range.contains(x))
                    .collect::<Vec<_>>()
                    .into_boxed_slice(),
            ),
        }
    }

    fn iter(&self, start: u8) -> FieldIter {
        match self.clone() {
            CronNormal::Val(val) => Box::new(iter::once((true, val))),
            CronNormal::Range(range, step) => {
                let mut iter = range
                    .clone()
                    .step_by(step as usize)
                    .enumerate()
                    .map(|(i, x)| (i == 0, x));

                for _ in range.step_by(step as usize).take_while(|&x| x < start) {
                    iter.next();
                }

                Box::new(iter)
            }
            CronNormal::Enums(enums) => {
                let skip = enums.iter().take_while(|x| **x < start).count();
                let mut iter = enums
                    .to_vec()
                    .into_iter()
                    .enumerate()
                    .map(|(i, x)| (i == 0, x));

                for _ in 0..skip {
                    iter.next();
                }

                Box::new(iter)
            }
        }
    }

    fn cycle_iter(&self, start: u8) -> FieldIter {
        match self.clone() {
            CronNormal::Val(val) => Box::new(iter::repeat((true, val))),
            CronNormal::Range(range, step) => {
                let mut iter = range
                    .clone()
                    .step_by(step as usize)
                    .enumerate()
                    .map(|(i, x)| (i == 0, x))
                    .cycle();

                for _ in range.step_by(step as usize).take_while(|&x| x < start) {
                    iter.next();
                }

                Box::new(iter)
            }
            CronNormal::Enums(enums) => {
                let skip = enums.iter().take_while(|x| **x < start).count();
                let mut iter = enums
                    .to_vec()
                    .into_iter()
                    .enumerate()
                    .map(|(i, x)| (i == 0, x))
                    .cycle();

                for _ in 0..skip {
                    iter.next();
                }

                Box::new(iter)
            }
        }
    }

    fn count(&self) -> usize {
        match self.clone() {
            CronNormal::Val(_) => 1,
            CronNormal::Range(range, step) => range.step_by(step as usize).count(),
            CronNormal::Enums(enums) => enums.len(),
        }
    }

    fn start(&self) -> u8 {
        match self {
            &CronNormal::Val(x) => x,
            CronNormal::Range(range, _) => *range.start(),
            CronNormal::Enums(enums) => enums[0],
        }
    }

    fn end(&self) -> u8 {
        match self {
            &CronNormal::Val(x) => x,
            CronNormal::Range(range, _) => *range.end(),
            CronNormal::Enums(enums) => *enums.last().unwrap(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DayOfMonth {
    Normal(CronNormal),
    LastWeekday,
    LastDayOfWeek(u8),
    Last,
    NearestWeekday(u8),
    NthDayMOfWeek { n: u8, m: u8 },
    None,
}

impl DayOfMonth {
    fn iter(&self, end: u8, day_of_week_of_start: u8) -> FieldIter {
        match self {
            DayOfMonth::Normal(f) => f.new_within_range(1..=end).iter(1),
            DayOfMonth::LastWeekday => {
                let day_of_week_of_end = (end + day_of_week_of_start - 1) % 7;
                let day = match day_of_week_of_end {
                    WEEKDAY_SUN => end - 2,
                    WEEKDAY_MON..=WEEKDAY_FRI => end,
                    WEEKDAY_SAT => end - 1,
                    _ => unreachable!(),
                };
                Box::new(iter::once((true, day)))
            }
            &DayOfMonth::LastDayOfWeek(last_day_of_week) => {
                let day_of_week_of_end = (end + day_of_week_of_start - 1) % 7;
                if day_of_week_of_end >= last_day_of_week {
                    Box::new(iter::once((
                        true,
                        end - (day_of_week_of_end - last_day_of_week),
                    )))
                } else {
                    Box::new(iter::once((
                        true,
                        end - (7 - (last_day_of_week - day_of_week_of_end)),
                    )))
                }
            }
            DayOfMonth::Last => Box::new(iter::once((true, end))),
            &DayOfMonth::NearestWeekday(day) if end < day => Box::new(iter::empty()),
            &DayOfMonth::NearestWeekday(day) => {
                let day_of_week = (day + day_of_week_of_start - 1) % 7;
                let weekday = match day_of_week {
                    WEEKDAY_SUN if day == end => day - 2,
                    WEEKDAY_SUN => day + 1,
                    WEEKDAY_MON..=WEEKDAY_FRI => day,
                    WEEKDAY_SAT => day - 1,
                    _ => unreachable!(),
                };
                Box::new(iter::once((true, weekday)))
            }
            &DayOfMonth::NthDayMOfWeek { n, m } => (1..=end)
                .zip(
                    (day_of_week_of_start..=(day_of_week_of_start + 7))
                        .map(|x| x % 7)
                        .cycle(),
                )
                .filter(|&(_, day_of_week)| day_of_week == m)
                .nth(n as usize)
                .map(|(day, _)| {
                    let iter: FieldIter = Box::new(iter::once((true, day)));
                    iter
                })
                .unwrap_or_else(|| Box::new(iter::empty())),
            DayOfMonth::None => Box::new(iter::empty()),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum DayOfWeek {
    Normal(CronNormal),
    None,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Day {
    DayOfMonth(DayOfMonth),
    DayOfWeek(DayOfWeek),
}

impl Day {
    fn iter(&self, end: u8, day_of_week_of_start: u8) -> FieldIter {
        match self {
            Day::DayOfMonth(f) => f.iter(end, day_of_week_of_start),
            Day::DayOfWeek(DayOfWeek::Normal(day_of_week)) => {
                Box::new(day_of_week.cycle_iter(day_of_week_of_start).scan(
                    (0u8, 0u8),
                    move |(prev_day, prev_day_of_week), (new_week, day_of_week)| {
                        let is_start = *prev_day == 0;
                        let day = if new_week {
                            *prev_day + 7 - (*prev_day_of_week - day_of_week)
                        } else {
                            *prev_day + (day_of_week - *prev_day_of_week)
                        };
                        *prev_day = day;
                        *prev_day_of_week = day_of_week;
                        (day <= end).then(|| (is_start, day))
                    },
                ))
            }
            Day::DayOfWeek(DayOfWeek::None) => unreachable!(),
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct CronExpr {
    pub second: CronNormal,
    pub minute: CronNormal,
    pub hour: CronNormal,
    pub day: Day,
    pub month: CronNormal,
}

impl CronExpr {
    pub fn parse(expr: &str) -> Result<Self, nom::error::Error<&str>> {
        crate::parser::parse_cron_expr(expr)
    }
}

pub struct CronIter {
    second: FieldIter,
    minute: FieldIter,
    hour: FieldIter,
    day: FieldIter,
    day_expr: Day,
    month: FieldIter,

    dt: NaiveDateTime,
}

fn end_of_month(year: i32, month: u8) -> u8 {
    let is_leap_year = if year % 100 == 0 {
        year % 400 == 0
    } else {
        year % 4 == 0
    };
    match month {
        4 | 6 | 9 | 11 => 30,
        2 if is_leap_year => 29,
        2 => 28,
        _ => 31,
    }
}

impl CronIter {
    fn next(&mut self) -> Option<NaiveDateTime> {
        let (is_start, second) = self.second.next()?;
        self.dt = self.dt.with_second(second as u32).unwrap();
        if !is_start {
            return Some(self.dt);
        }
        let (is_start, minute) = self.minute.next()?;
        self.dt = self.dt.with_minute(minute as u32).unwrap();
        if !is_start {
            return Some(self.dt);
        }
        let (is_start, hour) = self.hour.next()?;
        self.dt = self.dt.with_hour(hour as u32).unwrap();
        if !is_start {
            return Some(self.dt);
        }
        loop {
            if let Some((_, day)) = self.day.next() {
                self.dt = self.dt.with_day(day as u32).unwrap();
                return Some(self.dt);
            } else {
                let (is_start, month) = self.month.next()?;
                if is_start {
                    self.dt = self.dt.with_year(self.dt.year() + 1).unwrap();
                }
                self.dt = self.dt.with_month(month as u32).unwrap();
                self.day = self.day_expr.iter(
                    end_of_month(self.dt.year(), month),
                    self.dt
                        .with_day(1)
                        .unwrap()
                        .weekday()
                        .num_days_from_sunday() as u8,
                );
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_normal_field_iter() {
        let val = 1;
        let field = CronNormal::Val(val);
        assert_eq!(field.cycle_iter(val).next(), Some((true, val)));
        assert_eq!(field.cycle_iter(val + 1).next(), Some((true, val)));
        assert_eq!(
            field.cycle_iter(val).take(5).collect::<Vec<_>>(),
            iter::repeat((true, val)).take(5).collect::<Vec<_>>()
        );

        let field = CronNormal::Range(1..=12, 5);
        assert_eq!(field.cycle_iter(2).next(), Some((false, 6)));
        assert_eq!(field.cycle_iter(12).next(), Some((true, 1)));

        let field = CronNormal::Enums(vec![1, 3, 4].into_boxed_slice());
        assert_eq!(field.cycle_iter(1).next(), Some((true, 1)));
        assert_eq!(field.cycle_iter(5).next(), Some((true, 1)));
        assert_eq!(field.cycle_iter(2).next(), Some((false, 3)));
    }
}
