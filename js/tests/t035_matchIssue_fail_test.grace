method tryIt(a) {
    match(a) case { 1 → 
        print "a=1" 
    } case { s:String → 
        print "string {s}"
    } case { print "no argument here"
    } else {
        print "some other value ({a})"
    }
}

tryIt(5)
tryIt 1
