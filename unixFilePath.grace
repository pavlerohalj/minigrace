import "io" as io

type FilePath = EqualityObject & interface {
    directory -> String // the directory part; "./" if in current directory
    base -> String      // the base part of the file name (without an extension)
    extension -> String // the extension (like `.grace`) , including the `.`
    shortName -> String // the file name without the directory part
    quoted -> String    // the file name with internal special characters escaped
    inQuotes -> String  // the file name enclosed in quotes, and with internal
                        // special characters escaped

    directory:=(d)      // sets the directory part to d; answers done
    setDirectory(d)     // sets the directory part to d; answers self (for chaining)
    base:=(b)           // sets the base part of the file name to b; answers done
    setBase(b)          // sets the base part of the file name to b; answers self
    extension:=(e)      // sets the extension to e; answers done
    setExtension(e)     // sets the extension to e; answers self
    exists -> Boolean   // true if there is a file on this path
    newer(o) -> Boolean // true if this file is newer than o
    copy -> FilePath    // answers a new FilePath equal to self
    absolute -> FilePath  // answers a FilePath that reference the same file as self,
                          // but as a path from the file system root
}

class filePath {
    // creates a unixFilePath with empty components.
    // Why is this not called null?  Because that name emits confusing error
    // messages.  Instead, null redirects to this method.

    use equality

    var dir := ""
    // the directory part; "" if in current directory

    var base is public := ""
    // the base part of the file name (without an extension)

    var extension is public := ""
    // the extension (like `.grace`) , including the `.`

    method asString { dir ++ base ++ extension }
    // the whole file name as a string

    method quoted { asString.quoted }
    method inQuotes { "\"{quoted}\"" }

    method shortName { base ++ extension }
    // the file name without the directory part

    method asDebugString { "unixFilePath[{dir}|{base}|{extension}]" }
    // for debugging; shows the division into parts

    method directory {
    // the directory part; "./" if in current directory
        if (dir == "") then { "./" } else { dir }
    }

    method directory:=(d) {
    // set the directory part
        var newDir := d
        if (newDir == "") then {
            dir := ""
            return
        }
        if (newDir.at(newDir.size) != "/") then {
            newDir := newDir ++ "/"
        }
        if (newDir == "./") then { newDir := "" }
        dir := newDir
    }
    method setDirectory(d) {
    // set the directory part; answers self for chaining
        directory := d
        self
    }
    method setBase(b) {
    // set the base part; answers self for chaining
        base := b
        self
    }
    method setExtension(e) {
    // set the extension; answers self for chaining
        if (e.first == ".") then {
            extension := e
        } else {
            extension := "." ++ e
        }
        self
    }
    method exists -> Boolean {
    // true if his file exists
        io.exists(self.asString)
    }
    method newer(other) -> Boolean {
    // true if this file is newer than other
        io.newer(self.asString, other.asString)
    }

    method copy {
    // a copy of this filePath
        def p = filePath
        p.directory := directory
        p.base := base
        p.extension := extension
        p
    }

    method == (other) {
    // am I equal to other?
        if (directory != other.directory) then { return false }
        if (base != other.base) then { return false }
        if (extension != other.extension) then { return false }
        return true
    }

    method absolute {
        // make me an absolute, rather than relative, path
        directory := io.realpath(dir)
        self
    }

    method hash {
        hashCombine(hashCombine(directory.hash, base.hash), extension.hash)
    }
}

def null is public = object {
    inherit filePath
    method asString { "the null file" }
}

method withDirectory(d) {
    filePath.setDirectory(d)
}

method withBase(b) {
    filePath.setBase(b)
}

method withExtension(e) {
    filePath.setExtension(e)
}

method withDirectory(d) base(b) extension(e) {
    // creates a unixFilePath with directory d, base b and extension e
    filePath.setDirectory(d).setBase(b).setExtension(e)
}

method fromString(s) {
    // parses the filename s into components and answers the approriate unixFilePath
    def p = filePath
    var slashPosn := 0
    def sSize = s.size
    var ix := sSize
    while { (slashPosn == 0) && (ix > 0) } do {
        if (s.at(ix) == "/") then {
            slashPosn := ix
        } else {
            ix := ix - 1
        }
    }
    p.directory := s.substringFrom 1 to (slashPosn)
    var dotPosn := sSize + 1
    ix := sSize
    while { (dotPosn > sSize) && (ix > slashPosn) } do {
        if (s.at(ix) == ".") then {
            dotPosn := ix
        } else {
            ix := ix - 1
        }
    }
    if (dotPosn <= sSize) then {
        p.extension := s.substringFrom (dotPosn) to (sSize)
    }
    p.base := s.substringFrom (slashPosn + 1) to (dotPosn - 1)
    p
}

method split(pathString) {
    // splits pathString, assumed to be a Unix PATH containing items separated
    // by colons, into a List of items.  Ensures that each item ends with /
    def locations = list.empty
    var ix := 1
    var ox := 1
    def pss = pathString.size
    while { ox <= pss } do {
        while { (ox <= pss) && {pathString.at(ox) != ":"} } do {
            ox := ox + 1
        }
        var item := pathString.substringFrom(ix) to(ox-1)
        if (item.isEmpty.not) then {
            if (item.last != "/") then { item := item ++ "/" }
            locations.addLast (item)
        }
        ix := ox + 1
        ox := ix
    }
    return locations
}

method file(name) onPath(pathString) otherwise(action) {
    def locations = split(pathString)
    def candidate = name.copy
    def originalDir = name.directory
    if (originalDir.first == "/") then {
        if (candidate.exists) then {
            return candidate
        } else {
            return action.apply [originalDir]
        }
    }
    locations.do { each ->
        candidate.setDirectory(each ++ originalDir)
        if ( candidate.exists ) then {
            return candidate
        }
    }
    action.apply(locations)
}
