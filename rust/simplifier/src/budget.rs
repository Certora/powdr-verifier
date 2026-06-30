use std::time::{Duration, Instant};

const MARGIN: Duration = Duration::from_secs(2);

pub struct Budget {
    deadline: Option<Instant>,
}

impl Budget {
    pub fn from_timeout_secs(secs: f64) -> Self {
        if !secs.is_finite() || secs <= 0.0 {
            Self {
                deadline: Some(Instant::now()),
            }
        } else {
            Self {
                deadline: Some(Instant::now() + Duration::from_secs_f64(secs)),
            }
        }
    }

    pub fn unlimited() -> Self {
        Self { deadline: None }
    }

    pub fn remaining_for_pass(&self) -> Option<Duration> {
        self.deadline.map(|d| {
            d.saturating_duration_since(Instant::now())
                .saturating_sub(MARGIN)
        })
    }

    pub fn has_budget(&self) -> bool {
        match self.remaining_for_pass() {
            None => true,
            Some(d) => d > Duration::ZERO,
        }
    }
}
