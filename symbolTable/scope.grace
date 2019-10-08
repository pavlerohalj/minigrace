import "errormessages" as errormessages
import "nameDictionary" as nameDictionary
import "sourcePosition" as sourcePosition

def NamingError is public = errormessages.SyntaxError.refine "NamingError"

class graceBlockScope {
    inherit graceScope
}
type MinimalScope = interface {
    localNames → Collection
    reusedNames → Collection
}

def graceEmptyScope is public = object {
    // I represent the empty scope, with no definitions, and to which no definitions can be added.

    method isTheEmptyScope {
        return true
    }
//    method lookup (name) ifAbsent (aBlock) ifPresent (pBlock) {
//        return aBlock.apply
//    }
    def localNames is public = dictionary.empty
    def reusedNames is public = localNames
    method lookup (name) ifAbsent (aBlock) {
        return aBlock.apply
    }
    method lookup(name) { ProgrammingError.raise "{name} was not found in any lexical scope" }
    method lookupLocally (name) ifAbsent (aBlock) {
        return aBlock.apply
    }
    method localAndReusedNamesAndValuesDo (aBlock) {
        return self
    }
    method node {
        ProgrammingError.raise "the empty scope is not associated with a node"
    }
    method node := (nu) {
        ProgrammingError.raise "the empty scope cannot be associated with a node"
    }
    method asString {
        "the empty scope"
    }
    method add (aName) withName (aString) {
        ProgrammingError.raise("an attempt was made to add {aName.name} with " ++
            "name {aString} to a non-existant scope")
    }
    method lookupLocallyOrReused (name) ifAbsent (aBlock) {
        return aBlock.apply
    }
    method allNamesAndValuesDo (aBlock) {
        return self
    }
    method lookupLexically (name) ifAbsent (aBlock) {
        return aBlock.apply
    }
    method enclosingObjectScope {
        return self
    }
    method defines (name) {
        return false
    }
    method allNamesAndValuesDo (aBlock) filteringOut (closerDefinitions) {
        return self
    }
    method lookupLocallyOrReused (name) ifAbsent (aBlock) ifPresent (pBlock) {
        return aBlock.apply
    }
    method localNamesAndValuesDo (aBlock) {
        return self
    }
    method isObjectScope {
        // I'm treated as an object scope so that every non-empty scope has an enclosingObjectScope
        return true
    }
    method lookupLexically (name) ifAbsent (aBlock) ifPresent (pBlock) {
        return aBlock.apply
    }
    method outerScope {
        ProgrammingError.raise "the empty scope has no outerScope"
    }
    method outerScope := (nu) {
        ProgrammingError.raise "the empty scope cannot be given an outerScope"
    }
    method kind { "empty" }
}

def graceUniversalScope is public = object {
    inherit graceScope
    def universalVariable = singleton "universal variable"
    // I represent the universal scope, which defines all names

    method iterationError is confidential {
        ProgrammingError.raise "can't iterate through the Universal Scope"
    }
    method isTheEmptyScope { false }
    method lookup (name) ifAbsent (aBlock) ifPresent (pBlock) {
        pBlock.apply
    }
    method lookup (name) ifAbsent (aBlock) { universalVariable }
    method lookup(name) { universalVariable }
    method lookupLocally (name) ifAbsent (aBlock) { universalVariable }
    method localAndReusedNamesAndValuesDo (aBlock) { iterationError }
    method node {
        ProgrammingError.raise "the universal scope is not associated with a node"
    }
    method node := (nu) {
        ProgrammingError.raise "the universal scope cannot be associated with a node"
    }
    method asString {
        "the universal scope"
    }
    method add (aName) withName (aString) {
        ProgrammingError.raise("an attempt was made to add {aName.name} with " ++
            "name {aString} to the universal scope")
    }
    method lookupLocallyOrReused (name) ifAbsent (aBlock) { universalVariable }
    method allNamesAndValuesDo (aBlock) { iterationError }
    method lookupLexically (name) ifAbsent (aBlock) { universalVariable }
    method enclosingObjectScope { self }
    method defines (name) { true }
    method allNamesAndValuesDo (aBlock) filteringOut (closerDefinitions) {
        iterationError
    }
    method lookupLocallyOrReused (name) ifAbsent (aBlock) ifPresent (pBlock) {
        pBlock.apply
    }
    method localNamesAndValuesDo (aBlock) {
        iterationError
    }
    method isObjectScope {
        // I'm treated as an object scope so that every non-empty scope has an enclosingObjectScope
        true
    }
    method lookupLexically (name) ifAbsent (aBlock) ifPresent (pBlock) {
        pBlock.apply
    }
    method outerScope {
        ProgrammingError.raise "the universal scope has no outerScope"
    }
    method outerScope := (nu) {
        ProgrammingError.raise "the universal scope cannot be given an outerScope"
    }
    method kind { "universal" }
}
class graceInterfaceScope {
    inherit graceScope
    // I represent an iterface scope, that is, a set of methods.  Thus, I also represent the methods in an interface type.

    var outerScope is public

    method meet (anotherScope) {
        // create and return a new scope that is the mathematical meet of self and anotherTypeScope.
        // It contains those names common to both self and anotherScope.
        def result = graceInterfaceScope
        anotherScope.localNamesAndValuesDo { nm, rightVal →
            lookupLocally (nm) ifAbsent {
            } ifPresent { leftVal →
                result.add (leftVal.meet (rightVal)) withName (nm)
            }
        }
        return result
    }
    method join (anotherScope) {
        // create and return a new scope that is the mathematical join of self and anotherTypeScope.
        // it contains the definitions from both of these scopes.
        def result = self.copy
        anotherScope.localNamesAndValuesDo { nm, val →
            result.lookupLocally (nm) ifAbsent {
                result.add (val) withName (nm)
            } ifPresent { originalVal →
                result.redefine (val.join (originalVal)) withName (nm)
            }
        }
        return result
    }
    method kind { "interface" }
}
class graceMethodScope {
    inherit graceScope
        alias superAdd(_)withName(_) = add(_)withName(_)

    var outerScope is public

    method add (aVariable) withName (aString) {
        if (aVariable.isExplicitMethod) then {
            structuralError "sorry, you can't declare a method immediately inside a method" variable (aVariable)
        }
        return superAdd (aVariable) withName (aString)
    }
    method kind { "menthod" }
}
class graceObjectScope {
    // I represent an object scope in a Grace program.  I support reuse via
    // inheritance of objects and use of traits, and hence have an additional
    // dictionary for reused names.
    //
    // My fields are:
    //   reusedNames — a dictionary containing as keys all of the names reused
    //          (from a trait or superobject) in my scope.  This dictionary
    //          is polpulated on demand.
    //   statusOfReusedNames — one of "undiscovered", "inProgress", or "completed";
    //          the state of the process of collecting the reusedNames.

    inherit graceScope
        alias superCopy(other) = copy(other)


    var outerScope is public
    def reusedNames is public = nameDictionary.empty
    var statusOfReusedNames := "undiscovered"

    method markReusedNamesAsInProgress {
        statusOfReusedNames := "inProgress"
    }
    method isLegalAsTrait {
        return node.items.allSatisfy { each →
            each.isLegalInTrait
        }
    }
    method objectScope {
        return self
    }
    method addLocalAndReusedFrom (anotherScope) {
        anotherScope.localAndReusedNamesAndValuesDo { nm, defn →
            if (defn.isAvailableForReuse) then {
                addReused (defn) withName (nm)
            }
        }
    }
    method isReusable {
        // answer true if this scope can be reused and its definitions overridden.
        // If this objectScope stands as the initializer in a def, it can't be reused;
        // if it's inside a method, trait or class then it can be.
        node.isGraceClass || { node.parent.isMethod }
    }
    method addReused (aVariable) {
        addReused (aVariable) withName (aVariable.declaredName)
    }
    method localAndReusedNamesAndValuesDo (aBlock) filteringOut (closerDefinitions) {
        names.keysAndValuesDo { name, defn →
            if (closerDefinitions.includes (name).not) then {
                aBlock.apply (name) value (defn)
                closerDefinitions.add (name)
            }
        }
        reusedNames.keysAndValuesDo { name, defn →
            if (closerDefinitions.includes (name).not) then {
                aBlock.apply (name, defn)
                closerDefinitions.add (name)
            }
        }
    }
    method addReused (aVariable) withName (aName) {
        reusedNames.at (aName) put (aVariable)
        return aVariable
    }
    method isGenerative {
        print "aScope.isGenerative is deprecated — use aScope.isReusable"
        isReusable
    }
    method lookupReused (name) ifAbsent (aBlock) {
        // Return the variable corresponding to name, if it is defined in a scope that this
        // scope reuses.	If it is not defined, return the value of executing aBlock.
        if (areReusedNamesCompleted.not) then {
            ProgrammingError.raise ("reused names of {self} declared on " ++
                "{node.range.lineRangePrintString} have not been gathered")
        }
        return reusedNames.at (name) ifAbsent {
            aBlock.apply
        }
    }
    method reusedNamesAndValuesDo (aBlock) {
        reusedNames.keysAndValuesDo (aBlock)
    }
    method areReusedNamesInProgress {
        return (statusOfReusedNames == "inProgress")
    }
    method lookupReused (name) ifAbsent (aBlock) ifPresent (pBlock) {
        // If the variable corresponding to name is defined in a scope that this
        // scope reuses, apply pBlock to it and return the result.
        // If it is not defined, return the value of executing aBlock.
        if (areReusedNamesCompleted.not) then {
            ProgrammingError.raise ("reused names of {self} declared on " ++
                "{node.range.lineRangePrintString} have not been gathered")
        }
        def variable = reusedNames.at (name) ifAbsent {
            return aBlock.apply
        }
        return pBlock.apply (variable)
    }
    method copy(other) {
        def result = superCopy(other)
        other.reusedNames.keysAndValuesDo { name, variable →
            result.addReused(variable) withName (name)
        }
        result
    }
    method areReusedNamesCompleted {
        return (statusOfReusedNames == "completed")
    }
    method markReusedNamesAsCompleted {
        statusOfReusedNames := "completed"
    }
    method isObjectScope {
        return true
    }
    method kind { "object" }
}
class graceParameterScope {
    // A parameter scope is used to declare the type parameters and the value parameters
    // of a method.  Type parameters of a type go in the type scope.
    inherit graceScope

    var outerScope is public
    method kind { "parameter" }

}
class graceTypeScope {
    inherit graceScope
    // I record the names introduced by a type declaration.  These are the
    // parameters to the type, if any.
    // Nothing else goes in the type scope; the methods of an interface go in
    // an interface scope.
    var outerScope
    method kind { "type" }
}
class graceModuleScope {
    inherit graceObjectScope

    method isModuleScope { true }
    method lookup (name) ifAbsent (aBlock) {
        // Return the variable corresponding to name, which may or may not be defined in this scope,
        // or in the surroundng dialect scope, but no further.  If name is not defined, return the value
        // of executing aBlock.
        lookupLocallyOrReused (name) ifAbsent {
            outerScope.lookupLocallyOrReused (name) ifAbsent {
                aBlock.apply
            }
        }
    }
    method isReusable {
        // answer true if this scope can be reused and its definitions overridden
        false
    }
    method lookupLocallyOrOutwards (name) ifAbsent (aBlock) {
        // Return the variable corresponding to name, which may or may not be defined in this scope,
        // or in the lexically-enclosing dialect scope, but no further.  We do NOT look in the reused names of this scope. If name is not defined, return the value of executing aBlock.
        return lookupLocally (name) ifAbsent {
            outerScope.lookupLocallyOrReused (name) ifAbsent {
                aBlock.apply
            }
        }
    }
    method lookupLexically (name) ifAbsent (aBlock) {
        // Return the variable corresponding to name, which may or may not be defined in this scope, or in the surroundng dialect scope, but no further.  If name is not defined, return the value of executing aBlock.
        // Note that this method ignores reused names; it is intended for implementing Grace's shadowing check
        return lookupLocally (name) ifAbsent {
            outerScope.lookupLocally (name) ifAbsent {
                aBlock.apply
            }
        }
    }
    method importedModules {
        return names.values.select { each →
            each.isImport
        }
    }
    method kind { "module" }
}
class graceScope {
    // I represent a declaration scope in a Grace program.
    //
    // My fields are:
    //   names — a dictionary containing as keys all of the names declared in my scope.
    //          The values are the "variable" objects that represent the declaration.
    //   outerScope — the scope surrounding me, or emptyScope if there is none.

    def names = nameDictionary.empty
    var outerScope is public := graceEmptyScope
    var node is public

    method node(nu) {
        // sets the node for this scope, and returns self
        node := nu
        self
    }
    method lookup (name) ifAbsent (aBlock) {
        // Return the variable corresponding to name, which may or may not be
        // defined in this scope, or in one of the lexically surrounding scopes.
        // If it is not defined, return the value of executing aBlock.

        lookupLocallyOrReused (name) ifAbsent {
            outerScope.lookup (name) ifAbsent {
                aBlock.apply
            }
        }
    }
    method localAndReusedNamesAndValuesDo (aBlock) filteringOut (closerDefinitions) {
        names.keysAndValuesDo { name, defn →
            if (closerDefinitions.includes (name).not) then {
                aBlock.apply (name, defn)
                closerDefinitions.add (name)
            }
        }
    }
    method lookupLocally (name) ifAbsent (aBlock) ifPresent (pBlock) {
        // Look up variable corresponding to name, which may or may not be defined in this scope.
        // If it is not defined, return the result of executing aBlock; otherwise, the result of applying
        // pBlock to the variable.
        def variable = names.at (name) ifAbsent {
            return aBlock.apply
        }
        return pBlock.apply (variable)
    }
    method isReusable {
        // answer true if this scope is one that can be used or inherited
        false
    }
    method attributeScopeOf (aName) {
        lookup (aName).attributeScope
    }
    method asString {
        "scope containing " ++ names.keys.sorted
    }
    method lookupLocallyOrReused (name) ifAbsent (aBlock) {
        // Return the variable corresponding to name, which may or may not be defined in this scope,
        // or in one of the scopes that it reuses.
        // If name is not defined, return the value of executing aBlock.
        return lookupLocally (name) ifAbsent {
            lookupReused (name) ifAbsent {
                aBlock.apply
            }
        }
    }
    method copy(other) {
        def result = graceScope
        other.names.keysAndValuesDo { name, variable →
            result.add(variable) withName (name)
        }
        result.outerScope := graceEmptyScope
        result
    }
    method areReusedNamesCompleted {
        // Overriden in graceObjectScope
        return true
    }
    method enclosingObjectScope {
        var s
        s := self
        do {

        } while {
            s := s.outerScope.isObjectScope.not
        }
        return s
    }
    method reusedNames { dictionary.empty }
    method isModuleScope { false }
    method reuses (name) {
        // Is name defined by a scope that this scope reuses?
        false
    }
    method lookup (name) ifAbsent (aBlock) ifPresent (pBlock) {
        // applies pBlock to the variable corresponding to name, if it is defined in this scope,
        // or in one of the lexically surrounding scopes.  If it is not defined, return the value
        // of executing aBlock.
        lookupLocallyOrReused (name) ifAbsent {
            outerScope.lookup (name) ifAbsent (aBlock) ifPresent (pBlock)
        } ifPresent (pBlock)
    }
    method == (other) {
        match (other)
          case { sc:MinimalScope →
                (localNames.keys == sc.localNames.keys) && {
                    reusedNames.keys == sc.reusedNames.keys}
        } else {
            false
        }
    }
    method error (innerDefn) shadows (outerDefn) {
        NamingError.raise ("You can't use `{innerDefn.declaredName}` as the name " ++
              "of a {innerDefn.kind}, because `{innerDefn.declaredName}` " ++
              "is declared as a {outerDefn.kind} on {outerDefn.lineRangePrintString} " ++
              "in a surrounding scope; use a different name")
              with (innerDefn.definingParseNode)
    }
    method lookupLexically (name) {
        // Return the variable corresponding to name, which may or may not be
        // defined in this scope, or in one of the lexically surrounding scopes.
        // If name is not defined, return the value of executing aBlock.
        // Note that this method ignores reused names; it is intended for
        // implementing Grace's shadowing check
        lookupLexically (name) ifAbsent {
            NamingError.raise "{name} was not found in any lexical scope"
        }
    }
    method redeclarationError (aMessage) variable (aVariable) {
        NamingError.raise (aMessage) with (aVariable.definingParseNode)
    }
    method add (aVariable) withName (aName) {
        def priorDeclaration = names.at (aName) ifAbsent {
            names.at (aName) put (aVariable)
            return aVariable
        }
        NamingError.raise ("sorry, you can't declare `{aName}` as a " ++
              "{aVariable.kind}, because it's already declared as a "++
              "{priorDeclaration.kind} on {priorDeclaration.rangeLongPrintString}, " ++
              "which is in the same scope; use a different name")
              with (aVariable.definingParseNode)
    }
    method structuralError (aMessage) variable (aGraceAbstractVariable) {
        NamingError.raise (aMessage) with (aGraceAbstractVariable.definingParseNode)
    }
    method allNamesAndValuesDo (aBlock) {
        allNamesAndValuesDo (aBlock) filteringOut (Set.new)
    }
    method defines (name) {
        // Is name defined in this scope, or in one of the lexically surrounding scopes?
        definesLocallyOrReuses (name) || { outerScope.defines (name) }
    }
    method allNamesAndValuesDo (aBlock) filteringOut (closerDefinitions) {
        names.keysAndValuesDo { name, defn →
            if (closerDefinitions.includes (name).not) then {
                aBlock.apply (name, defn)
                closerDefinitions.add (name)
            }
        }
        reusedNames.keysAndValuesDo { name, defn →
            if (closerDefinitions.includes (name).not) then {
                aBlock.apply (name, defn)
                closerDefinitions.add (name)
            }
        }
        outerScope.allNamesAndValuesDo (aBlock) filteringOut (closerDefinitions)
    }
    method redefine (aVariable) withName (aName) {
        // overwites an existing defintion
        names.at (aName) put (aVariable)
        aVariable
    }
    method lookup (name) {
        // Retrieve the variable corresponding to name, which must be defined in this scope,
        // or in one of the lexically surrounding scopes.
        lookup (name) ifAbsent {
            NamingError.raise "{name} was not found in any lexical scope"
        }
    }
    method hash is abstract
    method isLegalAsTrait { false }
    method isTheEmptyScope { false }
    method reportShadowingErrors {
        names.keysAndValuesDo { name, defn →
            outerScope.lookup (name) ifAbsent {

            } ifPresent { outerDefn →
                error (defn) shadows (outerDefn)
            }
        }
    }
    method localAndReusedNamesAndValuesDo (aBlock) {
        localAndReusedNamesAndValuesDo (aBlock) filteringOut (Set.new)
    }
    method lookupReused (name) ifAbsent (aBlock) {
        // this is the default behaviour for scopes that don't allow reuse.  This method is overriden for  object scopes
        return aBlock.apply
    }
    method lookupReused (name) ifAbsent (aBlock) ifPresent (pBlock) {
        // this is the default behaviour for scopes that don't allow reuse.  This method is overriden for  object scopes
        return aBlock.apply
    }
    method lookupLexically (name) ifAbsent (aBlock) {
        // Return the variable corresponding to name, which may or may not be defined in this scope, or in one of the lexically surrounding scopes.  If name is not defined, return the value of executing aBlock.
        // Note that this method ignores reused names; it is intended for implementing Grace's shadowing check
        return lookupLocally (name) ifAbsent {
            outerScope.lookupLexically (name) ifAbsent {
                aBlock.apply
            }
        }
    }
    method definesLocallyOrReuses (name) {
        // Is name defined in this scope, or a scope that it reuses (ignoring surrounding scopes)
        return (names.includesKey (name) || {
            reuses (name)
        })
    }
    method dialectError (aString) {
        errormessages.CompilationError.raise (aString) with (sourcePosition.emptyRange)
    }
    method localNamesAndValuesDo (aBlock) {
        names.keysAndValuesDo (aBlock)
    }
    method removeReused (aName) ifAbsent (aBlock) {
        ProgrammingError.raise "a {kind} scope has no reused names"
    }
    method objectScope {
        return enclosingObjectScope
    }
    method lookupLocallyOrOutwards (name) ifAbsent (aBlock) {
        // Return the variable corresponding to name, which may or may not be defined in this scope,
        // or in one of the lexically-enclosing scopes.  We do NOT look in the reused names of this scope.
        // If name is not defined, return the value of executing aBlock.
        lookupLocally (name) ifAbsent {
            outerScope.lookup (name) ifAbsent {
                aBlock.apply
            }
        }
    }
    method add (aVariable) {
        add (aVariable) withName (aVariable.declaredName)
    }
    method localNames {
        names
    }
    method lookupLocally (name) ifAbsent (aBlock) {
        // Return the variable corresponding to name, which may or may not be defined in this scope.
        // If its is not defined, return the value of executing aBlock.
        names.at (name) ifAbsent {
            aBlock.apply
        }
    }
    method reusedNamesAndValuesDo (aBlock) {
        self
    }
    method definesLocally (name) {
        // Is name defined in this scope (ignoring surrounding scopes)
        names.at (name) ifAbsent {
            return false
        }.isConcrete
    }
    method doesNotDefineLocally (name) {
        definesLocally (name).not
    }
    method lookupLocallyOrReused (name) ifAbsent (aBlock) ifPresent (pBlock) {
        // applies pBlock to the variable corresponding to name, if it is defined in this scope,
        // or in one of the scopes that it reuses.
        // If name is not defined, return the value of executing aBlock.
        lookupLocally (name) ifAbsent {
            lookupReused (name) ifAbsent {
                aBlock.apply
            } ifPresent (pBlock)
        } ifPresent (pBlock)
    }
    method isObjectScope {
        false
    }
    method kind is abstract
}

class resolvedVariable(aVariable) {
    // My instances represent the defining occurence of a name, as seen from
    // the perspective of an applied occurrence of that name.
    // - definition: an subinstance of graceAbstractVariable, representing the defining occurence.
    // - objectsUp: the number of levels of object nesting above me where the
    // defining occurence was found.  0 means that the definiing occurence
    // is in the current object, 1 in the outer object, etc.
    // - isReused: true if the definition is obtained from a use of a trait, or from
    // an inherited object.

    def definition is public = aVariable
    var objectsUp is public
    var isReused is public  // true if this variable is accessible by virtue of a reuse (inherit or use) statement
    var levelsUp is public

    method resolutionString {
        // Answers a string, suitable for printing, that describes the location of this variable.
        return String.streamContents { s →
            (s << definition.kind << " " << reuseString << " by the ")
            if ((objectsUp == 0)) then {
                (s << "current")
            } else {
                (1 .. objectsUp ).do { _ →
                    (s << "outer")
                } separatedBy {
                    (s << ".")
                }
            }
            (s << " object")
        }
    }
    method reuseString {
        // Answers a string, suitable for printing, that describes my reuse.
        if (isReused) then {
             "reused "
        } else {
             "lexically-enclosing "
        }
    }
    method definingScope {
        // the scope in which this 'variable' is defined
        definition.definingParseNode.scope
    }
    method printStringOn (msg) {
        (msg << reuseString << definition.kind << " declared on " << definition.rangeLongPrintString)
    }
    method moduleName {
        // the name of the module in which this name was defined
        return definition.moduleName
    }
}
class variableResolver {
    method outerDefinitionOf (aName) in (aScope) addTo (aCollection) {
        // Looks for definitions of aName in the scopes surrounding aScope,
        // and adds the first one to aCollection, after tagging it with its
        // depth from our start point.  This method is complicated by the fact
        // that we stop searching one level above the first module, since that
        // scope is our dialect.

        var currentScope := aScope
        var objectLevel := 0
        var scopeLevel := 0
        while {
            currentScope.isModuleScope.not
        } do {
            scopeLevel := (scopeLevel + 1)
            if (currentScope.isObjectScope) then {
                objectLevel := (objectLevel + 1)
            }
            currentScope := currentScope.outerScope
            currentScope.lookupLocally (aName) ifAbsent {
                currentScope.lookupReused (aName) ifAbsent {

                } ifPresent { defn →
                    aCollection.add (reusedDefinition (defn) atObject (objectLevel)
                                levels (scopeLevel))
                    return aCollection
                }
            } ifPresent { defn →
                aCollection.add (definition (defn) atObject (objectLevel)
                            levels (scopeLevel))
                return aCollection
            }
        }
        def dialectDef = currentScope.outerScope.lookupLocallyOrReused (aName) ifAbsent {
            return aCollection
        }
        if (dialectDef.isPublic) then {
            if (currentScope.outerScope.definesLocally (aName)) then {
                aCollection.add (definition (dialectDef) atObject ((objectLevel + 1)) levels (scopeLevel))
            } else {
                aCollection.add (reusedDefinition (dialectDef) atObject ((objectLevel + 1)) levels (scopeLevel))
            }
        }
        return aCollection
    }
    method reusedDefinitionOf (aName) in (aScope) addTo (aCollection) {
        if (aScope.areReusedNamesCompleted.not) then {
            return aCollection
        }
        def defn = aScope.lookupReused (aName) ifAbsent {
            return aCollection
        }
        aCollection.add (reusedDefinition (defn))
        return aCollection
    }
    method definition (aVariable) atObject (o) levels (n) {
        def result = resolvedVariable (aVariable)
        result.isReused := false
        result.objectsUp := o
        result.levelsUp := n
        result
    }
    method lexicalOrLocalDefinitionOf (aName) in (aScope) ifPresent (pBlock) ifAbsent (aBlock) {
        // Look for a definition of aName in the nest of method and block scopes including and
        // surrounding aScope, but not outside the current object.  Don't look at reused names.
        // If aName is not found, applies aBlock; if it is found, applies pBlock to a ResolvedVariable
        // containing the definition.
        var currentScope := aScope
        while { true } do {
            currentScope.lookupLocally (aName) ifAbsent {
            } ifPresent { defn →
                return pBlock.apply (localDefinition (defn))
            }
            if (currentScope.isObjectScope) then {
                return aBlock.apply
            }
            currentScope := currentScope.outerScope
        }
    }
    method reusedDefinition (aVariable) {
        def result = resolvedVariable (aVariable)
        result.isReused := true
        result.objectsUp := 0
        result.levelsUp := 0
        result
    }
    method reusedDefinition (aVariable) atObject (o) levels (n) {
        def result = resolvedVariable (aVariable)
        result.isReused := true
        result.objectsUp := o
        result.levelsUp := n
        result
    }
    method localDefinition (aVariable) {
        def result = resolvedVariable (aVariable)
        result.isReused := false
        result.objectsUp := 0
        result.levelsUp := 0
        result
    }
    method definitionsOf (aName) visibleIn (aScope) {
        // answers a list of resolvedVariables describing the definitions of aName that
        // are visible from aScope. The collection is empty if there is no definition.
        // If aName is defined locally in aScope, then we allways answer a
        // singleton collection, ignoring inherited definitions and those in
        // outer scopes; this gives local definitions priority over inherited and
        // enclosing definitions. If aName is defined by inheritance _and_
        // in an outer scope, then the collection will have 2 elements.
        // In no case will it have more than 2 elements.

        lexicalOrLocalDefinitionOf (aName) in (aScope) ifPresent { defn →
            list.with(defn)
        } ifAbsent {
            def objectScope = aScope.objectScope
            def result = reusedDefinitionOf (aName) in (objectScope) addTo (list.empty)
            outerDefinitionOf (aName) in (objectScope) addTo (result)
        }
    }
}
