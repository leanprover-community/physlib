# physlibAlpha-worker

> This README contains a mermaid diagram, so should be viewed using a markdown viewer.

`physlibAlpha_worker.py` runs one task on PhyslibAlpha with an AI agent and opens a PR with the result. The numbers in the diagram are the sections of the script.

```mermaid
flowchart TD
    start(["physlibAlpha_worker.py [task] [input]"])
    subgraph setup ["Set up"]
        save["1. Find the save folder"]
        fork["2. Find or create the user's fork of physlib"]
        clone["3. Find or make a clone of the fork"]
        branch["4. Create a new branch from upstream/master"]
        agent["6. Choose the agent (Claude Code, else Codex)"]
        save --> fork --> clone --> branch --> agent
    end
    task["8. Read the task from physlibAlpha_worker.toml<br>and .agents/skills/(task)/SKILL.md"]
    runTask["9. The agent runs the task in the clone"]
    changed{"Anything changed?"}
    checks["10. Safety checks<br>only PhyslibAlpha changed, nothing deleted,<br>no new sorry, admit, axiom or native_decide,<br>PhyslibAlpha builds, linters pass"]
    pr["11. Commit, push and open a PR on upstream"]
    report["12. Do handbook alignment report and post on PR"]
    clean["13. Delete the branch and print a summary"]
    stop(["Stop with an error, leaving the clone as it is"])

    start --> setup --> task --> runTask --> changed
    changed -- no --> clean
    changed -- yes --> checks
    checks -- pass --> pr --> report --> clean
    checks -- fail --> stop
    runTask -- agent fails --> stop

    classDef ends fill:#e5e7eb,stroke:#6b7280,color:#111827
    classDef setupStep fill:#dbeafe,stroke:#3b82f6,color:#1e3a8a
    classDef agentStep fill:#ede9fe,stroke:#8b5cf6,color:#3b0764
    classDef checkStep fill:#fef3c7,stroke:#d97706,color:#78350f
    classDef prStep fill:#dcfce7,stroke:#16a34a,color:#14532d
    classDef failStep fill:#fee2e2,stroke:#dc2626,color:#7f1d1d

    class start,clean ends
    class save,fork,clone,branch,agent setupStep
    class task,runTask,report agentStep
    class changed,checks checkStep
    class pr prStep
    class stop failStep
    style setup fill:#eff6ff,stroke:#3b82f6,color:#1e3a8a
```
