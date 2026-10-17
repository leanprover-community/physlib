import json
import pandas as pd
import matplotlib.pyplot as plt

# JSON files to be imported, generate this with `lake exe graph physlib.xdot_json`
# See `https://github.com/leanprover-community/import-graph` for more info
graphFile = "physlib.xdot_json"

# Dictionary with keys ['name', 'directed', 'strict', '_subgraph_cnt', 'objects', 'edges']
physlib = json.load(open(graphFile))

# Dictionary with keys ['_gvid', 'name', 'fillcolor', 'label', 'shape', 'style']
files = physlib['objects']
# Dictionary with keys ['_gvid', 'tail', 'head']
# The 'tail' of an import arrow is the file being imported and the 'head' is the file doing the importing
imports = physlib['edges']

# Creates a dataframe with an entry for each file with its name, the indices of the files it imports, and the files that import it
physlib = pd.DataFrame([{'name':f['name'], 'imports':[], 'dependents':[]} for f in files])

# Total number of files in the project
numFiles = len(physlib)

# Adds the subject of the file (the name of the folder under physlib) to the datafram
physlib['subject'] = physlib.name.apply(lambda str: str.split('.')[1] if len(str.split('.')) > 1 else "Physlib" )

# The list of all current subjects in Physlib
subjectList = physlib.subject.unique()

# Builds the imports and dependents
for i in imports:
    physlib.dependents.loc[i['tail']].append(i['head'])
    physlib.imports.loc[i['head']].append(i['tail'])

# Returns the name of a file with a given index
def toName(index):
    return list(physlib.name.loc[index])

# Returns a list of the files imported by the file of a given index
def nameImports(index):
    return toName(physlib.imports.loc[index])

# Returns a list of the files that import the file of a given index
def nameDependents(index):
    return toName(physlib.dependents.loc[index])

# Returns the index of the file with the provided name
def toIndex(name):
    return physlib.index[physlib.name == name].tolist()

# Initialize the transitive import list
transImports = [None for i in range(len(physlib))]

# Generates the transitive imports for a given index
def genTransImports(index):
    # The transImports were already generated, skip
    if transImports[index] != None:
        return
    # The transImports starts with a copy of the direct imports
    transImports[index] = physlib.imports.loc[index].copy()
    # Adds the transImports of all direct imports, after possibly generating those lists
    for i in physlib.imports.loc[index]:
        genTransImports(i)
        transImports[index] += transImports[i]
    # Removes duplicate entries
    transImports[index] = list(set(transImports[index]))

# Generates the full list of transitive imports
for i in range(len(physlib)):
    genTransImports(i)

# Initialize the transitive dependents list
transDependents = [None for i in range(len(physlib))]

# Generates the transitive dependents for a given index
def genTransDependents(index):
    # The transDependents were already generated, skip
    if transDependents[index] != None:
        return
    # The transDependents starts with a copy of the direct dependents
    transDependents[index] = physlib.dependents.loc[index].copy()
    # Adds the transDependents of all direct dependents, after possibly generating those lists
    for i in physlib.dependents[index]:
        genTransDependents(i)
        transDependents[index] += transDependents[i]
    # Removes duplicate entries
    transDependents[index] = list(set(transDependents[index]))

# Generates the full list of transitive dependents
for i in range(len(physlib)):
    genTransDependents(i)

# Add transitive imports to dataframe
physlib['transImports'] = transImports
# Add transitive dependents to dataframe
physlib['transDependents'] = transDependents
# Add the number of transitive imports to dataframe
physlib['numTransImps'] = physlib.transImports.apply(len)
# Add the number of transitive dependents to dataframe
physlib['numTransDeps'] = physlib.transDependents.apply(len)

# Adds a measure of importance of a file to dataframe
# Importance is the product of % files transitively imported and % files transitively dependent
physlib['importance'] = physlib.apply(lambda x: (x.numTransImps/numFiles)*(x.numTransDeps/numFiles), axis=1)

# Plot the number of transitive dependents versus number of transitive imports
'''
plt.plot(physlib.numTransImps, physlib.numTransDeps, 'o')
plt.xlabel("# Transitive Imports")
plt.ylabel("# Transitive Dependents")
plt.show()
'''

# Plot a histogram of the importance of each file
'''
plt.hist(physlib.importance)
plt.xlabel("Importance")
plt.show()
'''
