use crate::expr::*;
use nom::{
    branch::alt,
    bytes::complete::tag_no_case,
    character::complete::{self as text, char, space0, space1},
    combinator::verify,
    multi::separated_list1,
    sequence::{separated_pair, terminated, tuple},
    Finish, IResult, Parser,
};

#[inline]
fn limited_u8<const MIN: u8, const MAX: u8>(input: &str) -> IResult<&str, u8> {
    verify(text::u8, |x| (MIN..=MAX).contains(x))(input)
}

fn cron_normal<'a, NumParser: FnMut(&'a str) -> IResult<&'a str, u8>>(
    num_parser: impl Fn() -> NumParser,
    min: u8,
    max: u8,
) -> impl FnMut(&'a str) -> IResult<&'a str, CronNormal> {
    assert!(min <= max);
    let all = char('*').map(move |_| CronNormal::Range(min..=max, 1));
    let enums = separated_list1(char(','), num_parser()).map(|mut e| {
        e.sort_unstable();
        e.dedup();
        if e.len() == 1 {
            CronNormal::Val(e[0])
        } else if (e.last().unwrap() - e[0] + 1) as usize == e.len() {
            CronNormal::Range(e[0]..=*e.last().unwrap(), 1)
        } else {
            CronNormal::Enums(e.into_boxed_slice())
        }
    });
    let range = tuple((num_parser(), char('-'), num_parser()))
        .map(|(start, _, end)| CronNormal::Range(start..=end, 1));
    let stepped_range = verify(
        tuple((num_parser(), char('/'), num_parser())),
        move |&(start, _, step)| (start + step) <= max,
    )
    .map(move |(start, _, step)| {
        CronNormal::Range(
            start..=((start..=max).step_by(step as usize).last().unwrap()),
            step,
        )
    });

    alt((all, range, stepped_range, enums))
}

fn month(input: &str) -> IResult<&str, CronNormal> {
    let num_parser = || {
        alt((
            limited_u8::<1, 12>,
            tag_no_case("JAN").map(|_| 1),
            tag_no_case("FEB").map(|_| 2),
            tag_no_case("MAR").map(|_| 3),
            tag_no_case("APR").map(|_| 4),
            tag_no_case("MAY").map(|_| 5),
            tag_no_case("JUN").map(|_| 6),
            tag_no_case("JUL").map(|_| 7),
            tag_no_case("AUG").map(|_| 8),
            tag_no_case("SEP").map(|_| 9),
            tag_no_case("OCT").map(|_| 10),
            tag_no_case("NOV").map(|_| 11),
            tag_no_case("DEC").map(|_| 12),
        ))
    };

    cron_normal(num_parser, 1, 12)(input)
}

fn day_of_month(input: &str) -> IResult<&str, DayOfMonth> {
    let num_parser = || limited_u8::<1, 31>;
    let cron_normal = cron_normal(num_parser, 1, 31).map(DayOfMonth::Normal);
    let none = char('?').map(|_| DayOfMonth::None);
    let last_day = char('L').map(|_| DayOfMonth::Last);
    let nearest_weekday = terminated(num_parser(), char('W')).map(DayOfMonth::NearestWeekday);

    alt((none, last_day, nearest_weekday, cron_normal))(input)
}

fn day_of_week(input: &str) -> IResult<&str, Day> {
    let day_of_week_ = || {
        alt((
            limited_u8::<1, 7>,
            tag_no_case("SUN").map(|_| 1),
            tag_no_case("MON").map(|_| 2),
            tag_no_case("TUE").map(|_| 3),
            tag_no_case("WED").map(|_| 4),
            tag_no_case("THU").map(|_| 5),
            tag_no_case("FRI").map(|_| 6),
            tag_no_case("SAT").map(|_| 7),
            char('L').map(|_| 7),
        ))
    };

    let cron_normal = cron_normal(day_of_week_, 1, 7).map(|f| Day::DayOfWeek(DayOfWeek::Normal(f)));
    let none = char('?').map(|_| Day::DayOfWeek(DayOfWeek::None));
    let last_day_of_week = terminated(day_of_week_(), char('L'))
        .map(|x| Day::DayOfMonth(DayOfMonth::LastDayOfWeek(x)));
    let nth_day_m_of_week = separated_pair(day_of_week_(), char('#'), limited_u8::<1, 6>)
        .map(|(m, n)| Day::DayOfMonth(DayOfMonth::NthDayMOfWeek { n, m }));

    alt((none, last_day_of_week, nth_day_m_of_week, cron_normal))(input)
}

pub fn parse_cron_expr(input: &str) -> Result<CronExpr, nom::error::Error<&str>> {
    let second = cron_normal(|| limited_u8::<0, 59>, 0, 59);
    let minute = cron_normal(|| limited_u8::<0, 59>, 0, 59);
    let hour = cron_normal(|| limited_u8::<0, 23>, 0, 23);

    let day_and_month = verify(
        tuple((day_of_month, space1, month, space1, day_of_week)),
        |(day_of_month, _, _, _, day_of_week)| {
            matches!(day_of_month, DayOfMonth::None)
                != matches!(day_of_week, Day::DayOfWeek(DayOfWeek::None))
        },
    )
    .map(|(day_of_month, _, month, _, day_of_week)| {
        (
            if matches!(day_of_month, DayOfMonth::None) {
                Day::DayOfMonth(day_of_month)
            } else {
                day_of_week
            },
            month,
        )
    });

    tuple((
        space0,
        second,
        space1,
        minute,
        space1,
        hour,
        space1,
        day_and_month,
        space0,
    ))
    .map(
        |(_, second, _, minute, _, hour, _, (day, month), _)| CronExpr {
            second,
            minute,
            hour,
            day,
            month,
        },
    )
    .parse(input)
    .finish()
    .map(|(_, cron)| cron)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_limited_u8() {
        assert_eq!(limited_u8::<1, 12>("1"), Ok(("", 1)));
        assert!(limited_u8::<1, 12>("13").is_err());
    }

    #[test]
    fn test_cron_normal() {
        let mut parse_cron_normal = cron_normal(|| limited_u8::<1, 12>, 1, 12);

        assert_eq!(parse_cron_normal("1"), Ok(("", CronNormal::Val(1))));
        assert_eq!(
            parse_cron_normal("*"),
            Ok(("", CronNormal::Range(1..=12, 1)))
        );
        assert_eq!(
            parse_cron_normal("3/5"),
            Ok(("", CronNormal::Range(3..=12, 5)))
        );
        assert_eq!(
            parse_cron_normal("3-5"),
            Ok(("", CronNormal::Range(3..=5, 1)))
        );
        assert_eq!(
            parse_cron_normal("3,4,5"),
            Ok(("", CronNormal::Range(3..=5, 1)))
        );
        assert_eq!(
            parse_cron_normal("3,5"),
            Ok(("", CronNormal::Enums(vec![3, 5].into_boxed_slice())))
        );
    }

    #[test]
    fn test_month() {
        assert_eq!(month("1"), Ok(("", CronNormal::Val(1))));
        assert_eq!(month("JaN"), Ok(("", CronNormal::Val(1))));
        assert_eq!(month("JAN-JUL"), Ok(("", CronNormal::Range(1..=7, 1))));
    }

    #[test]
    fn test_day_of_month() {
        assert_eq!(
            day_of_month("1"),
            Ok(("", DayOfMonth::Normal(CronNormal::Val(1))))
        );
        assert_eq!(day_of_month("?"), Ok(("", DayOfMonth::None)));
        assert_eq!(day_of_month("L"), Ok(("", DayOfMonth::Last)));
        assert_eq!(
            day_of_month("15W"),
            Ok(("", DayOfMonth::NearestWeekday(15)))
        );
    }

    #[test]
    fn test_day_of_week() {
        assert_eq!(
            day_of_week("1"),
            Ok(("", Day::DayOfWeek(DayOfWeek::Normal(CronNormal::Val(1)))))
        );
        assert_eq!(
            day_of_week("SuN"),
            Ok(("", Day::DayOfWeek(DayOfWeek::Normal(CronNormal::Val(1)))))
        );
        assert_eq!(
            day_of_week("SUN-THU"),
            Ok((
                "",
                Day::DayOfWeek(DayOfWeek::Normal(CronNormal::Range(1..=5, 1)))
            ))
        );
        assert_eq!(
            day_of_week("L"),
            Ok(("", Day::DayOfWeek(DayOfWeek::Normal(CronNormal::Val(7)))))
        );
        assert_eq!(day_of_week("?"), Ok(("", Day::DayOfWeek(DayOfWeek::None))));
        assert_eq!(
            day_of_week("SUNL"),
            Ok(("", Day::DayOfMonth(DayOfMonth::LastDayOfWeek(1))))
        );
        assert_eq!(
            day_of_week("SUN#3"),
            Ok((
                "",
                Day::DayOfMonth(DayOfMonth::NthDayMOfWeek { m: 1, n: 3 })
            ))
        );
    }
}
