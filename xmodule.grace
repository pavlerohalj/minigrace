import "io" as io
import "sys" as sys
import "util" as util
import "ast" as ast
import "mirrors" as mirrors
import "errormessages" as errormessages
import "unixFilePath" as filePath


def CheckerFailure = Exception.refine "CheckerFailure"
def DialectError is public = Exception.refine "DialectError"
    //must correspond to what is defined in "dialect"

def gctCache = emptyDictionary
def keyCompare = { a, b -> a.key.compare(b.key) }

def builtInModules =
             [  "mirrors",
                "sys",
                "unicode" ]

method isBuiltInModule(name) {
    builtInModules.contains(name)
}

def currentDialect is public = object {
    var name is public := "standardGrace"
    var moduleObject is public := prelude
    // TODO: this isn't quite right: should be the prelude
    // on the GRACE_MODULE_PATH of this compilation
    var hasParseChecker is public := false
    var hasAstChecker is public := false
    var hasAtStart is public := false
    var hasAtEnd is public := false
}

type LinePos = {
    line -> Number
    linePos -> Number
}

type RangeSuggestions = {
    line -> Number
    posStart -> Number
    posEnd -> Number
    suggestions
}

def dynamicCModules is public = set ["mirrors", "curl", "unicode"]
def imports = util.requiredModules

method checkDialect(moduleObject) {
    def dialectNode = moduleObject.theDialect
    def dmn = dialectNode.moduleName
    currentDialect.name := dmn
    if (dmn == "none") then { return }
    util.log 50 verbose "checking dialect {dmn} used by module {moduleObject.name}"
    checkExternalModule(dialectNode)
    def dialectGct = gctDictionaryFor(dialectNode.path)
    if ((dialectGct.at "public" ifAbsent {emptySequence}).contains "thisDialect") then {
        util.log 50 verbose "loading dialect \"{dmn}\" for checkers."
        try {
            def dobj = mirrors.loadDynamicModule(dialectNode.path)
            currentDialect.moduleObject := dobj
            if (mirrors.reflect(dobj).methodNames.contains "thisDialect") then {
                def mths = mirrors.reflect(dobj.thisDialect).methods
                for (mths) do { m ->
                    if (m.name == "parseChecker(_)") then {
                        currentDialect.hasParseChecker := true
                    }
                    if (m.name == "astChecker(_)") then {
                        currentDialect.hasAstChecker := true
                    }
                    if (m.name == "atEnd(_)") then {
                        currentDialect.hasAtEnd := true
                    }
                    if (m.name == "atStart(_)") then {
                        currentDialect.hasAtStart := true
                    }
                }
            }
        } catch { e:Exception ->
            util.setPosition(dialectNode.line, 1)
            e.printBacktrace
            errormessages.error "Dialect error: dialect \"{dmn}\" failed to load.\n{e}."
                atLine(dialectNode.line)
        }
    } else {
        util.log 50 verbose "no need to load dialect \"{dmn}\": it does not define `thisDialect`"
    }
}

method doParseCheck(moduleNode) {
    if (currentDialect.hasParseChecker.not) then { return }
    try {
        currentDialect.moduleObject.thisDialect.parseChecker(moduleNode)
    } catch { e:CheckerFailure | DialectError | errormessages.SyntaxError ->
        reportDialectError(e)
    } catch { e:Exception ->      // some unknown Grace exception
        printBacktrace (e) asFarAs "thisDialect.parseChecker"
        errormessages.error("Unexpected exception raised by parse checker for " ++
            "dialect '{currentDialect.name}'.\n{e.exception}: {e.message}")
    }
}

method doAstCheck(moduleNode) {
    if (currentDialect.hasAstChecker.not) then { return }
    try {
        currentDialect.moduleObject.thisDialect.astChecker(moduleNode)
    } catch { e:CheckerFailure | DialectError | errormessages.SyntaxError ->
        reportDialectError(e)
    } catch { e:Exception ->      // some unknown Grace exception
        printBacktrace (e) asFarAs "thisDialect.astChecker"
        errormessages.error("Unexpected exception raised by AST checker for " ++
            "dialect '{currentDialect.name}'.\n{e.exception}: {e.message}")
    }
}

method reportDialectError(ex) {
    match (ex.data)
      case { rs:RangeSuggestions ->
        errormessages.error "Dialect {currentDialect.name}: {ex.message}."
            atRange(rs)
            withSuggestions(rs.suggestions)
    } case { r:ast.Range ->  //  inlcudes ast.AstNode
        errormessages.error "Dialect {currentDialect.name}: {ex.message}."
            atRange(r)
    } case { p:ast.Position ->
        errormessages.error "Dialect {currentDialect.name}: {ex.message}."
            atPosition(p.line, p.column)
    } else {
        errormessages.error "Dialect {currentDialect.name}: {ex.message}."
            atLine(util.linenum)
    }
}

method printBacktrace(exceptionPacket) asFarAs (methodName) {
    def ex = exceptionPacket.exception
    def msg = exceptionPacket.message
    def lineNr = exceptionPacket.lineNumber
    def mod = exceptionPacket.moduleName
    if (lineNr == 0) then {
        io.error.write "{ex} in {mod}: {msg}\n"
    } else {
        io.error.write "{ex} on line {lineNr} of {mod}: {msg}\n"
    }
    def bt = exceptionPacket.backtrace
    while {bt.size > 0} do {
        def frameDescription = bt.pop
        io.error.write "  requested from {frameDescription}\n"
        if (frameDescription.contains(methodName)) then { return }
    }
}

method checkExternalModule(node) {
    checkimport(node.moduleName, node.path, node.isDialect, node.range)
}

method checkimport(nm, pathname, isDialect, sourceRange) is confidential {
    if (imports.isAlready(nm)) then {
        return
    }

    if (inBrowser) then {
        util.file(nm ++ ".js") onPath "" otherwise { _ ->
            errormessages.error "Please \"Run\" module {nm} before importing it."
                atRange(sourceRange)
        }
        return
    }
    util.log 50 verbose "checking module \"{nm}\""
    def gmp = sys.environ.at "GRACE_MODULE_PATH"
    def pnJs = filePath.fromString(pathname).setExtension "js"
    def pnGrace = pnJs.copy.setExtension "grace"
    def files = list [pnJs, pnGrace]
    if (isBuiltInModule(nm)) then {
        files.addLast (pnJs.copy.setExtension "gct")
    }
    var moduleFile := util.firstFile(files) on (util.sourceDir)
                                orPath (gmp) otherwise { m ->
        def rm = errormessages.readableStringFrom(m)
        errormessages.error("I can't find {pnJs.shortName} " ++
            "or {pnGrace.shortName}; looked in {rm}.") atRange (sourceRange)
    }
    if (moduleFile.extension == ".grace") then {
        util.log 50 verbose "about to compile module \"{nm}\""
        def objectFile = compileModule (nm) inFile (moduleFile)
                forDialect (isDialect) atRange (sourceRange)
        if (objectFile.exists.not) then {
            errormessages.error("I just compiled {moduleFile}, " ++
                "but {objectFile} does not exist") atRange (sourceRange)
        }
        moduleFile := objectFile
    }
    util.log 50 verbose "found module \"{nm}\" in {moduleFile}"

    def gctDict = gctDictionaryFor(nm) from (moduleFile)
    def sourceFile = filePath.fromString(gctDict.at "path" .first)
    def sourceExists = if (sourceFile.directory.contains "stub") then {
        false        // for binary-only modules like unicode
    } else {
        sourceFile.exists
    }
    if ( util.target == "js" ) then {
        if (moduleFile.exists && {
            sourceExists.not || { moduleFile.newer(sourceFile) }
        }) then {
        } else {
            if (moduleFile.newer(sourceFile).not) then {
                util.log 60 verbose "{moduleFile} not newer than {sourceFile}"
            }
            if (sourceFile.exists) then {
                compileModule (nm) inFile (sourceFile)
                    forDialect (isDialect) atRange (sourceRange)
            } else {
                def thing = if (isDialect) then {"dialect"} else {"module"}
                errormessages.error "Can't find {thing} {nm}"
                    atRange(sourceRange)
            }
        }
        imports.other.add(nm)
    }
    addTransitiveImports(moduleFile.directory, isDialect, nm, sourceRange)
}

method addTransitiveImports(directory, isDialect, moduleName, sourceRange) is confidential {
    def gctDict = gctCache.at(moduleName) ifAbsent {
        parseGCT(moduleName) sourceDir(directory)
    }
    if (gctDict.containsKey "dialect") then {
        def dialects = gctDict.at "dialect"
        if (dialects.isEmpty.not) then {
            def dName = gctDict.at "dialect" .first
            checkimport(dName, dName, true, sourceRange)
        }
    }
    def importedModules = gctDict.at "modules" ifAbsent { emptySequence }
    def m = util.modname
    if (importedModules.contains(m)) then {
        errormessages.error("Cyclic import detected: '{m}' is imported "
            ++ "by '{moduleName}', which is imported by '{m}' (and so on).")
            atRange(sourceRange)
    }
    importedModules.do { each ->
        checkimport(each, each, isDialect, sourceRange)
    }
}

method compileModule (nm) inFile (sourceFile)
        forDialect (isDialect) atRange (sourceRange) is confidential {
    // Compiles module with name nm located in sourceFile.
    // Returns the filePath containing the compiled code.

    if (util.recurse.not) then {
        errormessages.error "Please compile module {nm} before using it."
            atRange (sourceRange)
    }
    if (inBrowser) then {
        errormessages.error "Please \"Run\" module {nm} before using it."
            atRange (sourceRange)
    }
    var cmd
    if (sys.argv.first.contains "/") then {
        cmd := io.realpath(sys.argv.first)
    } else {
        cmd := io.realpath "{sys.execPath}/{sys.argv.first}"
    }
    cmd := "\"{cmd}\""
    cmd := cmd.replace "compiler-js" with "minigrace-js"
    if (util.verbosity != util.defaultVerbosity) then {
        cmd := cmd ++ " --verbose {util.verbosity}"
    }
    var outputDirectory
    if (util.dirFlag) then {
        cmd := cmd ++ " --dir " ++ util.outDir
        outputDirectory := util.outDir
    } else {
        outputDirectory := sourceFile.directory
    }
    if (false != util.vtag) then {
        cmd := cmd ++ " --vtag " ++ util.vtag
    }
    cmd := cmd ++ " --gracelib " ++ util.gracelibPath
    cmd := cmd ++ util.commandLineExtensions
    cmd := "{cmd} --target {util.target} --make \"{sourceFile}\""
    util.log 50 verbose "executing sub-compile {cmd}"
    def exitCode = io.spawn("bash", ["-c", cmd]).status
    if (exitCode != 0) then {
        errormessages.error "Failed to compile imported module {nm} ({exitCode})."
            atRange (sourceRange)
    }
    filePath.withDirectory(outputDirectory) base(sourceFile.base) extension ".js"
}

method gctDictionaryFor(moduleName) from (moduleFile) is confidential {
    // Returns the GCT dictionary for moduleName, extracting it from
    // moduleFile if necesssary

    gctCache.at(moduleName) ifAbsent {
        parseGCT(moduleName) sourceDir(moduleFile.directory)
    }
}

method gctDictionaryFor(moduleName) {
    gctCache.at(moduleName) ifAbsent {
        if (inBrowser) then {
            gctDictionaryFrom(extractGctFromCache(moduleName)) for(moduleName)
        } else {
            ProgrammingError.raise "gct dictionary for {moduleName} not in cache"
        }
    }
}

method parseGCT(moduleName) sourceDir(dir) is confidential {
    // Returns the GCT dictionary for moduleName

    // We extract the GCT string from an external resource, parse it,
    // and build and return a new dictioanry containing the "GCT information",
    // which describes the objects exported from moduleName

    gctDictionaryFrom(extractGctFor(moduleName) sourceDir(dir)) for(moduleName)
}

method gctDictionaryFrom(gctList) for(moduleName) is confidential {
    def gctDict = dictionary.empty
    var key := ""
    for (gctList) do { line ->
        if (line.size > 0) then {
            if (line.first ≠ " ") then {
                key := line.substringFrom 1 to (line.size-1)  // dropping the ":"
                gctDict.at(key) put(list [ ])
            } else {
                gctDict.at(key).addLast(line.substringFrom 2 to (line.size))
            }
        }
    }
    gctCache.at(moduleName) put(gctDict)
    gctDict
}


method extractGctFor(moduleName) sourceDir(dir) is confidential {
    // Extracts the gct information for moduleName from an external resource
    // Returns the gct information as a collection of Strings.

    if (inBrowser) then { return extractGctFromCache(moduleName) }
    try {
        try {
            return extractGctFromJsFile(moduleName) sourceDir(dir)
        } catch { ep:EnvironmentException ->
            done
        } // other exceptions are deliberately not caught

        return extractGctFromGctFile(moduleName) sourceDir(dir)
    } catch {ex:EnvironmentException ->
        util.log 0 verbose("Failed to find gct for {moduleName}; " ++
            "looked in {dir} for a .js file containing a gct string, and a .gct file.")
        sys.exit(2)
    }
}

method extractGctFromJsFile(moduleName) sourceDir(dir) is confidential {
    // Looks for a .js file containing the compiled code for moduleName.
    // The file that referenced moduleName is in directory dir.
    // Returns the gct information as a collection of Strings.

    def sought = filePath.fromString(moduleName).setExtension ".js"
    def gmp = sys.environ.at "GRACE_MODULE_PATH"
    def filename = util.file(sought) on(dir) orPath(gmp) otherwise { l ->
        def rl = errormessages.readableStringFrom(l)
        EnvironmentException.raise "Can't find file {sought} for module {moduleName}; looked in {rl}."
    }
    def jsStream = io.open(filename, "r")
    var maxLines := 10  // look in first 10 lines of js file
    while { jsStream.eof.not && (maxLines > 0) } do {
        def line = jsStream.getline
        if (line.startsWith "  gctCache[") then {
            jsStream.close
            return splitJsString(line)
        }
        maxLines := maxLines - 1
    }
    jsStream.close
    EnvironmentException.raise "Can't find gct string in JS file {filename}"
}

method extractGctFromGctFile(moduleName) sourceDir(dir) is confidential {
    // Looks for a .gct file continaing the compiled code for moduleName.
    // The file that referenced moduleName is in directory dir.
    // Returns the gct information as a collection of Strings.
    def sought = filePath.fromString(moduleName).setExtension ".gct"

    def gmp = sys.environ.at "GRACE_MODULE_PATH"
    def filename = util.file(sought) on(dir) orPath(gmp) otherwise { l ->
        def rl = errormessages.readableStringFrom(l)
        EnvironmentException.raise "Can't find file {sought} for module {moduleName}; looked in {rl}."
    }
    def gctStream = io.open(filename, "r")
    def result = list []
    while { gctStream.eof.not } do {
        result.push(gctStream.getline)
    }
    result
}

method splitJsString(jsLine:String) is confidential {
    // jsLine is a line of javascript like
    //   gctCache["xmodule"] = "classes:\nconfidential:\n CheckerFailure\n ..."
    // Evaluates the string on the rhs of the = sign, splits into lines,
    // and returns a (Grace) list containing those lines as (Grace) strings.
    native "js" code ‹
        var arg = var_jsLine._value;
        var keyStr = "\"] = ";
        var keyStart = arg.indexOf(keyStr);
        var stringLit = arg.substr(keyStart + keyStr.length);
        var gctString = eval(stringLit);
        var jsStringArray = gctString.split("\n");
        result = GraceList([]);
        for (var ix = 0, len = jsStringArray.length ; ix < len; ix++) {
            callmethod(result, "push(1)", [1],
                new GraceString (jsStringArray[ix]));
        }›
}

method extractGctFromCache(module) {
    // When running in the browser, returns a Grace list containing
    // the contents of the cached gct information for module

    native "js" code ‹var gctString = gctCache[var_module._value];
        var jsStringArray = gctString.split("\n");
        result = GraceList([]);
        for (var ix = 0, len = jsStringArray.length ; ix < len; ix++) {
            callmethod(result, "push(1)", [1],
                new GraceString (jsStringArray[ix]));
        }›
}


method writeGCT(modname, dict) is confidential {
    if (util.extensions.containsKey "gctfile") then {
        def fp = io.open("{util.outDir}{modname}.gct", "w")
        list.withAll(dict.bindings).sortBy(keyCompare).do { b ->
            fp.write "{b.key}:\n"
            list.withAll(b.value).sort.do { v ->
                fp.write " {v}\n"
            }
        }
        fp.close
    }
    gctCache.at(modname) put(dict)
}

method writeGctForModule(moduleObject) {
    writeGCT(moduleObject.name, generateGctForModule(moduleObject))
}

method gctAsString(gctDict) {
    var ret := ""
    list.withAll(gctDict.bindings).sortBy(keyCompare).do { b ->
        ret := ret ++ "{b.key}:\n"
        list.withAll(b.value).sort.do { v ->
            ret := ret ++ " {v}\n"
        }
    }
    return ret
}

var methodtypes := list [ ]
def typeVisitor = object {
    inherit ast.baseVisitor
    var literalCount := 1

    method visitIdentifier(ident) {
        methodtypes.push("& {ident.value}")
        return false
    }

    method visitMember(member) {
        return false
    }

    method visitTypeLiteral(lit) {
        for (lit.methods) do { meth ->
            var mtstr := "{literalCount} "
            for (meth.signature) do { part ->
                mtstr := mtstr ++ part.name
                if (part.params.size > 0) then {
                    mtstr := mtstr ++ "("
                    for (part.params.indices) do { pnr ->
                        var p := part.params.at(pnr)
                        if (p.dtype != false) then {
                            mtstr := mtstr ++ p.toGrace(1)
                        } else {
                            // if parameter type not listed, give it type Unknown
                            if(p.wildcard) then {
                                mtstr := mtstr ++ "_"
                            } else {
                                mtstr := mtstr ++ p.value
                            }
                            mtstr := mtstr ++ ":" ++ ast.unknownType.value
                            if (false != p.generics) then {
                                mtstr := mtstr ++ "⟦"
                                for (1..(p.generics.size - 1)) do {ix ->
                                    mtstr := mtstr ++ p.generics.at(ix).toGrace(1) ++ ", "
                                }
                                mtstr := mtstr ++ p.generics.last.toGrace(1) ++ "⟧"
                            }
                        }
                        if (pnr < part.params.size) then {
                            mtstr := mtstr ++ ", "
                        }
                    }
                    mtstr := mtstr ++ ")"
                }
            }
            if (meth.rtype != false) then {
                mtstr := mtstr ++ " → " ++ meth.rtype.toGrace(1)
            }
            methodtypes.push(mtstr)
        }
        return false
    }
    method visitOp(op) {
        if ((op.value=="&") || (op.value=="|")) then {
            def leftkind = op.left.kind
            def rightkind = op.right.kind
            if { leftkind=="typeliteral" } then {
                literalCount := literalCount + 1
                methodtypes.push("{op.value} {literalCount}")
                visitTypeLiteral(op.left)
            } elseif { leftkind=="op" } then {
                visitOp(op.left)
            } else {
                var typeIdent := op.left.toGrace(0)
                methodtypes.push("{op.value} {typeIdent}")
            }
            if { rightkind=="typeliteral" } then {
                literalCount := literalCount + 1
                methodtypes.push("{op.value} {literalCount}")
                visitTypeLiteral(op.right)
            } elseif { rightkind=="op" } then {
                visitOp(op.right)
            } else {
                var typeIdent := op.right.toGrace(0)
                methodtypes.push("{op.value} {typeIdent}")
            }
        }
        return false
    }
}
method generateGctForModule(moduleObject) is confidential {
    def gct = buildGctFor(moduleObject)
    addFreshMethodsOf (moduleObject) to (gct)
    return gct
}

method generateMethodHeader(methNode) -> String {
    var depth: Number := 0
    var s: String := ""
    var firstPart := true
    for (methNode.signature) do { part ->
        s := s ++ part.name
        if (firstPart && {false != methNode.typeParams}) then {
            s := s ++ methNode.typeParams.toGrace(depth + 1)
        }
        firstPart := false
        if (part.params.size > 0) then {
            s := s ++ "("
            for (part.params.indices) do { pnr ->
                var p := part.params.at(pnr)
                s := s ++ p.toGrace(depth + 1)
                if (pnr < part.params.size) then {
                    s := s ++ ", "
                }
            }
            s := s ++ ")"
        }
    }
    if (false != methNode.dtype) then {
        s := s ++ " → {methNode.dtype.toGrace(0)}"
    }
    s
}

method buildGctFor(module) {
    def gct = emptyDictionary
    def classes = emptyList
    def confidentials = emptyList
    def meths = set.empty    // this must be a set, because the same name may be added
        // from a module.parent's providedNames, and a body node that is a method.
    def types = emptyList
    def publicMethodTypes = emptyList
    def theDialect = module.theDialect.moduleName
    module.parentsDo { p ->
        meths.addAll(p.providedNames)       // add inherited and used methods
    }
    for (module.value) do { v->
        // TODO: replace this scan of the whole module by traversal of the
        // module symbol table
        if (v.kind == "vardec") then {
            def gctType = if (false != v.dtype) then {v.dtype.toGrace(0)} else {"Unknown"}
            def varRead: String = "{v.name.value} → {gctType}"
            if (v.isReadable) then {
                meths.add(v.name.value)
                publicMethodTypes.push(varRead)
                gct.at("publicMethod:{v.name.value}") put(list[varRead])
            } else {
                confidentials.push(v.name.value)
            }

            def varWrite: String = "{v.name.value}:=({v.name.value}': " ++
                                                            "{gctType}) → Done"
            if (v.isWritable) then {
                meths.add(v.name.value ++ ":=(1)")
                publicMethodTypes.push(varWrite)
                gct.at("publicMethod:{v.name.value}:=(1)") put(list[varWrite])
            } else {
                confidentials.push(varWrite)
            }
        } elseif {v.kind == "method"} then {
            if (v.isPublic) then {
                meths.add(v.nameString)
                publicMethodTypes.push(generateMethodHeader(v))
                gct.at("publicMethod:{v.nameString}") put([generateMethodHeader(v)])
            } else {
                confidentials.push(v.nameString)
            }
        } elseif {v.kind == "typedec"} then {
            if (v.isPublic) then {
                meths.add(v.nameString)
                types.push(v.nameWithParams)
                methodtypes := list [ ]
                v.value.accept(typeVisitor)
                gct.at "methodtypes-of:{v.nameWithParams}" put(methodtypes)
                gct.at "typedec-of:{v.nameWithParams}" put([v.toGrace(0)])
            } else {
                confidentials.push(v.nameString)
            }

        } elseif {v.kind == "defdec"} then {
            if (v.isPublic) then {
                meths.add(v.nameString)
                def gctType = if (false != v.dtype) then {v.dtype.toGrace(0)} else {"Unknown"}
                publicMethodTypes.push("{v.name.value} → {gctType}")
                gct.at("publicMethod:{v.name.value}") put (list["{v.name.value} → {gctType}"])
            } else {
                confidentials.push(v.nameString)
            }
            if (v.returnsObject) then {
                def ob = v.returnedObjectScope.node
                def obConstructors = list [ ]
                if (ob.isObject) then {
                  for (ob.value) do {nd->
                    if (nd.isClass) then {
                        def factMethNm = nd.nameString
                        obConstructors.push(factMethNm)
                        def exportedMethods = emptyList
                        ob.scope.getScope(factMethNm).keysAndKindsDo { key, knd ->
                            if (knd.forGct) then { exportedMethods.add(key) }
                        }
                        gct.at "methods-of:{v.name.value}.{factMethNm}"
                            put(exportedMethods.sort)
                    }
                  }
                }
                if (obConstructors.size > 0) then {
                    gct.at "constructors-of:{v.name.value}"
                        put(obConstructors)
                    classes.push(v.name.value)
                }
            }
        } elseif {v.kind == "import"} then {
            if (v.isPublic) then {
                meths.add(v.nameString)
                def gctType = if (false != v.dtype) then {v.dtype.toGrace(0)} else {"Unknown"}
                publicMethodTypes.push("{v.name.value} → {gctType}")
            } else {
                confidentials.push(v.nameString)
            }
        }
    }
    gct.at "classes" put(classes.sort)
    gct.at "confidential" put(confidentials.sort)
    gct.at "modules" put(list.withAll(module.imports).sorted)
    def p = util.infile.pathname
    gct.at "path" put [ if (p.isEmpty) then {
        ""
    } elseif { p.startsWith "/" } then {
        p
    } else {
        io.realpath(p)
    } ]
    gct.at "public" put(list.withAll(meths).sort)
    gct.at "publicMethodTypes" put(publicMethodTypes.sort)
    gct.at "types" put(types.sort)
    gct.at "dialect" put (
        if (theDialect == "none") then { [] } else { [theDialect] }
    )
    gct
}

method addFreshMethodsOf (moduleObject) to (gct) is confidential {
    // adds information about the methods made available via fresh methods.
    // This is done in a separate pass after public information is in the gct,
    // because of the special treatment of prelude.clone
    // TODO: doesn't this just duplicate what's in 'classes' ? No: 'classes'
    // lists only classes declared inside a def'd object constructor, i.e.,
    // something simulating he old "dotted" class
    def freshmeths = list [ ]
    for (moduleObject.value) do { node->
        if (node.isClass) then {
            addFreshMethod (node) to (freshmeths) for (gct)
        }
    }
    gct.at "fresh-methods" put(freshmeths)
}

method addFreshMethod (node) to (freshlist) for (gct) is confidential {
    def methName = node.nameString
    freshlist.push(methName)
    def freshMethExpression = node.body.last
    if (freshMethExpression.isObject) then {
        def exportedMethods = emptyList
        freshMethExpression.scope.keysAndKindsDo { key, knd ->
            if (knd.forGct) then { exportedMethods.add(key) }
        }
        gct.at "fresh:{methName}" put (exportedMethods.sort)
    } elseif {freshMethExpression.isCall} then {
        // this deals with the two special cases, defined in
        // ast.callNode.returnsObject.  The freshMethExpression must
        // be a request of self.copy or prelude.clone(_)
        def requestedName = freshMethExpression.nameString
        if (requestedName == "copy") then {
            gct.at "fresh:{methName}" put(gct.at "public")
        } elseif {requestedName == "clone(1)"} then {
            def cloneArg = freshMethExpression.parts.first.args.first
            if (cloneArg.isSelf) then {
                gct.at "fresh:{methName}" put(gct.at "public")
            } else {
                gct.at "fresh:{methName}"
                    put(gct.at "methods-of:{cloneArg.toGrace 0}" isAbsent {
                        ProgrammingError.raise (
                            "unrecognized fresh method tail-call:\n" ++
                              freshMethExpression.pretty(0) ++ "\n" ++
                                "Can't find methods-of:{cloneArg.toGrace 0} in gct." )
                } )
            }
        } else {
            // if it's not a call or an object constructor, why is it labelled as fresh?
            ProgrammingError.raise
                "unrecognized fresh method tail-call: {freshMethExpression.pretty(0)}"
        }
    } else {
        ProgrammingError.raise
            "fresh method result of an unexpected kind: {freshMethExpression.pretty(0)}"
    }
}
