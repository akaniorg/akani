# Design

**This document is a work in progress and will be updated as development continues. It describes akani's "production" version running against an S3 object store and k8s cluster, although there will be a local mode for testing and small-scale deployments.**

Akani aims to provide two key capabilities:

- Changing input locations in an S3 bucket automatically runs user-defined code to produce results (job orchestration / execution).

- Any object in the bucket can be traced to the inputs and code which produced it (lineage).

Akani leverages industry-standard tools to achieve these goals. S3 serves as the store for reading and writing objects. Crucially it also stores [akani metadata](#metadata): there is no separate database that needs to be kept in sync with the object store, the objects themselves contain all lineage information. Job execution is handled by [k8s jobs](https://kubernetes.io/docs/concepts/workloads/controllers/job/).


## User experience

Akani is designed for scientists and incorporates real-world lessons from building data-centric systems in R&D. A key lesson is that scientists, like most, already deal with a plethora of interfaces to do their job (ELNs, molecule registries, bio databases, instrument control software, data backups), so leveraging familiar GUIs makes any new tool much more productive. This motivates akani's use of S3 as the object store: upload a file and the result will appear, all within the same interface already used for data sharing and backups.

The above describes the user experience for *data generators*, who care about results but not how they are produced. The second user group are *scientific developers* who would like their analyses to run in an automated fashion. Akani uses [pipeline definitions](#pipeline-definition) to describe which code runs on which inputs. While this introduces a new interface, it aims to link to familiar concepts. The main constraint in the definition file is that the object store locations read by user code, as well as result locations written to, must be spelled out explicitly. The goal is for user code to only worry about S3 I/O. Containerisation, orchestration and scaling will be hidden for common use cases by providing "data science images" with pre-installed packages.


## The pipeline process

The below steps describe how pipelines execute.

1. An input change is detected either by scanning the object store or by receiving an event. The former will be expensive for large numbers of inputs so should be avoided for production, but is useful for running periodic consistency checks.

2. Akani finds other relevant inputs by scanning the object store locations given in the [pipeline definition](#pipeline-definition), as well as existing results. Each set of matching inputs is called a 'datum' (borrowing [pachyderm](https://www.pachyderm.com/) terminology) which is processed separately. Akani sorts each datum into the following categories:
   - A result object exists:
     - The result metadata matches the input objects -> `DONE`
     - The result metadata doesn't match the input objects -> start job, `STALE`
     - An older version of the result object matches the inputs -> restore, `RESTORABLE`
     - The result object doesn't have metadata -> start job, `MANUAL`
   - No result object -> start job, `TODO`

3. (For a full scan of the object store, there may also be result objects which don't have matching inputs. This adds a `DANGLING` category.)

4. Datum jobs are passed to the executor which runs the user-defined code. Akani relies on the user to only read from locations specified as inputs and write results to pre-defined locations. This is similar to [dvc](https://dvc.org/) but unlike [pachyderm](https://www.pachyderm.com/), which uses filesystem magic to provide guardrails. The akani approach creates friction because users need to update the pipeline definition every time they change a write location in their code. This is deemed acceptable because it avoids having to wrap / infiltrate user code, instead treating it as a black box.

5. The executor reports finished jobs back to akani. Akani attaches metadata to the results objects written by the job. Similarly to the previous point, separating the writing of results from attaching metadata simplifies reasoning about user code as a black box. However it requires careful consideration of failure modes:
   - Changing the result object between the user code writing it and akani attaching metadata leads to a fatally inconsistent state where the result is wrongly associated with the inputs. This is a race condition between akani and whichever other process changes the same location. In terms of akani internals, it must be ensured that jobs from the same pipeline **writing to the same result location** are never executed in parallel but queued. A likely scenario are multiple uploads which overwrite the same object and produce multiple jobs, all of which write back to the same location. Akani needs to synchronise each input version with the corresponding result.

     On the user side, there needs to be clear guidance on which actions result in an inconsistent state. Result locations should never be manually written to. This may be enforceable with S3 permissions, but cannot be prevented by akani itself.
   - The akani process may be terminated while jobs are still running, producing valid result objects which don't have metadata attached to them. This doesn't affect consistency and is straightforward to recognise as a `MANUAL` datum (see step 2) during the next scan, but means the same job will need to be recomputed.

6. To start downstream pipelines, akani can either use knowledge of the DAG or wait for events reporting the changed upstream result objects.


## Q&A

The below qualitatively describes what needs to happen inside akani to retrieve information which users may find useful.

- Which code and inputs produced a given result object?

    Read the result object metadata to find the pipeline and inputs which produced it. To find all related upstream objects repeatedly read the metadata on inputs.

- Which downstream results does an object affect?

    Akani internally represents the set of pipelines as a DAG. Walk forwards through the graph. This means an akani instance must always know about all pipelines comprising a DAG.

- Which jobs changed an object store location?

    Iterate through versions and read metadata.

- Which jobs have run?

    Scan result locations for objects with metadata, read jobs. This will be much less performant than a separate metadata store maintaining a list of jobs, see the [metadata section](#metadata) for trade-offs.

- Which objects were involved in a particular job?

    Scan result locations and read metadata. To find all involved objects across the DAG, proceed as described in the first two questions.
 

## Pipeline definitions

These contain input locations, code to run on the input objects and the location to which results will be written.

- **Inputs**

    Similar to the [pachyderm pipeline spec](https://docs.pachyderm.com/latest/build-dags/pipeline-spec/). Akani adds joins on named glob capture groups, so that for
    ```
    - name: Input_A
      glob: /<COMPONENT_A>/<COMPONENT_B>/foo.bar
    - name: Input_B
      glob: baz/<COMPONENT_A>/<COMPONENT_B>/foo.bar
    ```
    the path components `<COMPONENT_A>` and `<COMPONENT_B>` must both match.

- **Code**

    TODO

- **Results**

    TODO


## Metadata

Information about their lineage is attached to result objects directly using [tags](https://docs.aws.amazon.com/AmazonS3/latest/userguide/object-tagging.html). There is a limit of 10 tags per object, which puts a constraint on the number of inputs an object can depend on. This has to be weighed against the convenience of not having to deal with "sidecar" files or a separate metadata store.

TODO define metadata format


## Observability

Akani should provide access to job logs. Depending on the k8s setup this may not be straightforward, particularly for autoscaling clusters where nodes disappear once jobs are finished. TODO investigate [CloudWatch](https://aws.amazon.com/cloudwatch/) or equivalent log collectors.


## Visualisation 

There are no plans for akani to provide a visual interface. [Marquez](https://marquezproject.ai/) on top of [OpenLineage](https://openlineage.io/) may be used to show the pipeline DAG and jobs, but the object store metadata will remain the single source of truth.


## Open questions

- How are pipelines themselves versioned? 

    Akani's ability to provide accurate lineage information relies on knowing the definitions of the pipelines which produced an object. Object metadata includes information about the pipeline, but this doesn't guarantee that any running akani instance is aware of a particular pipeline version. **Object store metadata is only a useful single source of truth in combination with pipeline definitions.** A possible solution is a central version-controlled repository containing definitions, with akani loading all DAGS, including historical ones.


