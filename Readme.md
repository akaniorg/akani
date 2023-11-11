**Prototype, under heavy development and not ready for use**.

Built for science at [Transition Bio](https://github.com/transitionbio).

# akani

**Minimalist data pipelines with lineage.**

The workflow:

- Write a [pipeline definition](docs/design.md#pipeline-definitions) that tells akani about inputs, the code that should run on them and where results will be written.
- Upload input files.
- Run akani or wait for the daemon to do its thing. It will figure out which code needs to run in response to the changed inputs and add lineage metadata to the results.
- Sleep easy knowing that for any result you'll be able to answer the question: Which code has produced this object based on which inputs?


## Yet another data versioning / pipelining / job orchestration tool?

Yes. Akani is inspired by [dvc](https://dvc.org/) and [pachyderm](https://www.pachyderm.com/) and designed based on experience running both in production. It attempts to combine the best of both worlds by following a few principles:

- **Simple but scalable**
    Akani stays nimble by offloading the heavy lifting to established tools. [S3](https://aws.amazon.com/s3) does the data versioning. [k8s](https://kubernetes.io/docs/concepts/workloads/controllers/job/) orchestrates jobs. Or just run it locally with nothing but a filesystem and a few commands.

- **Hassle-free job orchestration**
    Akani kicks off jobs based on flexible input definitions, including [pachyderm](https://www.pachyderm.com/)-inspired wildcards to deal with continuously added files. Jobs only run for changed inputs without existing results, keeping compute and costs down.

- **Full lineage**
    Always know where an object comes from. Akani prioritises consistency, so it will never leave things in a broken state without telling you how to fix it.


## When is akani **not** for you?

- Very high job throughput. Akani is designed to handle a steady rate of compute-intensive jobs, not a flood of small ones. The current [design](docs/design.md) does not envision distributed deployment, although that may change in the future. Note that you can scale by stitching together multiple pipeline [DAGs](https://en.wikipedia.org/wiki/Directed_acyclic_graph) by linking upstream results to downstream inputs and running a separate akani instance for each DAG, although you lose traceability through the global DAG. **There aren't any measurements yet about what "very high throughput" means. Akani is designed to deal with imaging data for high-throughput drug screening assays, so short of building the next viral web platform it'll likely be performant enough for most R&D applications.**

- You don't care about versioning / lineage and just want a DAG of Python functions to execute. Use [dagster](https://dagster.io/) or [prefect](http://prefect.io/) or [airflow](https://airflow.apache.org/) or one of the many orchestration tools out there.

- You need git-like data versioning including branches and snapshot "time-travel". Akani leverages S3 as the object store so you're limited to object versions. For "git-for-data"-like functionality check out [dvc](https://dvc.org/), [lakefs](https://lakefs.io/), [pachyderm](https://www.pachyderm.com/) or trouble your favourite search engine.

- [Data deduplication](https://en.wikipedia.org/wiki/Data_deduplication) is required. You get what S3 gives you. Note that it may be possible to replace S3 with a different object store in the future.


## Design

See the [design document](docs/design.md) for the key ideas.


## Progress

- [x] S3 path glob parser, including named capture groups.
- [x] Lazy, cached datum generator for `join` pipeline inputs. All glob capture groups must match and all inputs be present unless declared `optional`. Tested against S3.
- [ ] Consistent input specification. `join`, `union`, `cross`? Nesting?
- [ ] Pipeline definition format & parser.
- [ ] Walkable pipeline DAG representation for multiple DAG versions, see [design](docs/design.md#open-questions).
- [ ] Metadata specification.
- [ ] S3 interface to read / write metadata and receive "object changed" events.
- [ ] k8s interface for job execution & tracking.
- [ ] Daemon server mode & cloud deployment.
- [ ] ... continuously updated.

