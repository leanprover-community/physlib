import os
import plotly.express as px   # to generate the plot
from git import Repo           # gitpython to analyze the repo
import numpy as np
import pandas as pd

repo = Repo(".")               
physlean_path = os.path.join(repo.working_tree_dir, "PhysLean")   # to analyze folders in the PhysLean folder in main branch (other folders like docs, scripts are ignored)

# all folders in Physlean are named after a branch of physics, we assign a number to each branch to generate colors on treemap based on categories (Stats mech is 1, classical mech is 2 ..)
folders = [name for name in os.listdir(physlean_path) if os.path.isdir(os.path.join(physlean_path, name))]
folder_map = {folder: idx + 1 for idx, folder in enumerate(folders)}

#debugging
#print(folder_map)

##################################################### names that end with a "." are actually ending with .lean but lean is removed for visibility

#generating the tree for treemap, id has to be unique and is assigned the absolute path, label is what is displayed, this is immediate file or folder name for visibility
# size decides the area occupied by each label, here it is just the file size, value is what decides the color, here it is the number assigned to the parent folder, so each file inside stats mech is assigned same number
blobs = [{
    'parent': os.path.dirname(blob.path) or "/",
    'id': blob.path,
    'labeling': blob.path.rsplit("/", 1)[-1].removesuffix("lean"),
    'size': blob.size,

    #'commits': len(commits := list(repo.iter_commits(paths=blob.path))),
    'value': (
        folder_map.get(blob.path.split("/")[1], 0)
        if len(blob.path.split("/")) > 1 and blob.path.startswith("PhysLean/")
        else 0
    )} for blob in repo.tree().traverse() if "PhysLean" in blob.path.rsplit("/", 1)[0]]

print(blobs[-1])



fig = px.treemap(
blobs,
    names='labeling',
    ids = 'id',
    parents='parent',
    labels = 'labeling',
    color='value',
    #hover_data=['commits'],
    values='size',

    color_continuous_scale='plasma'
)
fig.write_image("docs/treemap.png",
width=1600,    # pixels
    height=1200,   # pixels
    scale=2        # multiplies resolution (like DPI scaling)
               )
