atom completionPercent(active: i64, done: i64) -> i64
    requires: active >= 0 && done >= 0 && done <= active;
    ensures: (active == 0 => result == 0) && result >= 0 && result <= 100;
    body: { if active == 0 { 0 } else { done * 100 / active } }
