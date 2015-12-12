dialect "minitest"

method for (cs) and (ds) do (action) -> Done {
    def dIter = ds.iterator
    cs.do { c -> 
        if (dIter.hasNext) then {
            action.apply(c, dIter.next)
        } else {
            return
        }
    }
}

testSuiteNamed "for and" with {
    test "same size" by {
        def result = list.empty
        def as = [1, 2, 3, 4, 5]
        def bs = ["one", "two", "three", "four", "five"]
        for (as) and (bs) do { a, b ->
            result.add(a::b)
        }
        assert (result) shouldBe
            (list.with(1::"one", 2::"two", 3::"three", 4::"four", 5::"five"))
    }
    
    test "first smaller" by {
        def result = list.empty
        def as = [1, 2, 3]
        def bs = ["one", "two", "three", "four", "five"]
        for (as) and (bs) do { a, b ->
            result.add(a::b)
        }
        assert (result) shouldBe
            (list.with(1::"one", 2::"two", 3::"three"))
    }
    
    test "second smaller" by {
        def result = list.empty
        def as = [1, 2, 3, 4, 5]
        def bs = ["one", "two", "three"]
        for (as) and (bs) do { a, b ->
            result.add(a::b)
        }
        assert (result) shouldBe
            (list.with(1::"one", 2::"two", 3::"three"))
    }
    
    test "first empty" by {
        def result = list.empty
        def as = []
        def bs = ["one", "two", "three"]
        for (as) and (bs) do { a, b ->
            result.add(a::b)
        }
        assert (result) shouldBe (list.empty)
    }
    
    test "second empty" by {
        def result = list.empty
        def as = [1, 2, 3, 4, 5]
        def bs = []
        for (as) and (bs) do { a, b ->
            result.add(a::b)
        }
        assert (result) shouldBe (list.empty)
    }
    
    test "both empty" by {
        def result = list.empty
        def as = []
        def bs = []
        for (as) and (bs) do { a, b ->
            result.add(a::b)
        }
        assert (result) shouldBe (list.empty)
    }
}