use std::backtrace::Backtrace;

#[derive(Debug)]
pub struct MonkeError(String, Backtrace);

impl PartialEq for MonkeError {
    fn eq(&self, other: &Self) -> bool {
        self.0 == other.0
    }
}

impl MonkeError {
    pub fn new(msg: impl Into<String>) -> Self {
        MonkeError(msg.into(), Backtrace::capture())
    }
}

impl<T> From<MonkeError> for std::result::Result<T, MonkeError> {
    fn from(value: MonkeError) -> Self {
        Err(value)
    }
}

impl std::fmt::Display for MonkeError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "{}\nMESSAGE: {}\nBACKTRACE: \n{}",
            std::any::type_name_of_val(self),
            self.0,
            self.1.to_string()
        )
    }
}

impl std::error::Error for MonkeError {}
