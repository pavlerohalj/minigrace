dialect "standard"
type Date = interface {
    year -> Number
        // the year, e.g., 2016
    month -> Number
        // the month, e.g, for 1 for January, 4 for April
    date -> Number
        // the day of the month, from 1 to 31
    day -> Number
        // the day of the week, e.g. 1 for Sunday, 1 for Monday
    hour -> Number
        // the hour of the day, e.g. 16 for 4 pm
    minute -> Number
        // the minutes past the hour, e.g. 49 for 4:49 pm
    second -> Number
        // the seconds past the minute, e.g. 32 for 4:49:32 pm
    asString -> String
        // a string representation of this date and time
    asDateString -> String
        // a string representation of just the date part
    asTimeString -> String
        // a string representation of just the time part
    asIsoString -> String
        // a string representation that complies with ISO 8601
    timeZoneOffsetInMinutes -> Number
        // the offset between this time and UTC, in minutes.
    timeZoneOffsetInHours -> Number
        // the offset between this time and UTC, in hours.
    == (other:Date) -> Boolean
        // is self == to other?
    + (other:Date) -> Date
        // the sum of self and other
    - (other:Date)
        // the difference betweem self and other
    * (factor:Number)
        // the product of self and factor
}

trait basic {
    // all in local time

    use equality
    method year -> Number {
        // the year, e.g., 2016
        native "js" code "return new GraceNum(this.data.value.getFullYear())"
    }
    method month -> Number {
        // the month, e.g, for 1 for January, 4 for April
        native "js" code "return new GraceNum(this.data.value.getMonth() + 1)"
    }
    method date -> Number {
        // the day of the month, from 1 to 31
        native "js" code "return new GraceNum(this.data.value.getDate())"
    }
    method day -> Number {
        // the day of the week, e.g. 1 for Sunday, 2 for Monday
        native "js" code "return new GraceNum(this.data.value.getDay() + 1)"
    }
    method hour -> Number {
        // the hour of the day, e.g. 16 for 4 pm
        native "js" code "return new GraceNum(this.data.value.getHours())"
    }
    method minute -> Number {
        // the minute past the hour, e.g. 49 for 4:49 pm
        native "js" code "return new GraceNum(this.data.value.getMinutes())"
    }
    method second -> Number {
        // the second past the minute, e.g. 33 for 4:49:33 pm
        native "js" code "return new GraceNum(this.data.value.getSeconds())"
    }
    method millisecond -> Number {
        // the second past the minute, e.g. 33 for 4:49:33 pm
        native "js" code "return new GraceNum(this.data.value.getMilliseconds())"
    }    
    method asString -> String {
        native "js" code "return new GraceString(this.data.value.toString())"
    }
    method asDateString -> String {
        native "js" code "return new GraceString(this.data.value.toDateString());"
    }
    method asTimeString -> String {
        native "js" code "return new GraceString(this.data.value.toTimeString());"
    }
    method asIsoString -> String {
        native "js" code "return new GraceString(this.data.value.toISOString());"
    }
    method asMilliseconds -> Number {
        // date as milliseconds since the epoch
        native "js" code "return new GraceNum(this.data.value.getTime());"
    }
    method timeZoneOffsetInMinutes -> Number {
        // the offset between this time and UTC, as a Number of minutes.

        // why not present this as a date?  Because, as a date, it's always zero
        native "js" code "return new GraceNum(this.data.value.getTimezoneOffset());"
    }
    method timeZoneOffsetInHours -> Number {
        // the offset between this time and UTC, as a Number of hours.
        native "js" code "return new GraceNum(this.data.value.getTimezoneOffset() / 60);"
    }
    method + (other:Date) -> Date {
        milliseconds(self.asMilliseconds + other.asMilliseconds)
    }
    method - (other:Date) -> Date {
        milliseconds(self.asMilliseconds - other.asMilliseconds)
    }    
    method * (factor:Number) -> Date {
        milliseconds(self.asMilliseconds * factor)
    }    
    method reverseTimesNumber (factor:Number) -> Date {
        milliseconds(factor * self.asMilliseconds)
    }
    method == (other:Date) -> Boolean {
        self.asMilliseconds == other.asMilliseconds
    }
}

class milliseconds(n) -> Date {
    // n milliseconds since the epoch 
    inherit basic
    def value = native "js" code "result = new Date(var_n._value);"
}
    
method seconds(n) -> Date {
    // n seconds in milliseconds
    milliseconds(1000 * n)
}

method minutes(n) -> Date {
    seconds(60 * n)
}

method hours(n) -> Date {
    minutes(60 * n)
}

method days(n) -> Date {
    hours(24 * n)
}

method weeks(n) -> Date {
    days(7 * n)
}

class now {
    inherit basic
    def value = native "js" code "result = new Date();"
}

class fromString(dateString) {
    inherit basic
    def value = native "js" code "result = new Date(var_dateString._value);"
}

    
