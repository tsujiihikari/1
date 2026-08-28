-- ============================================================
-- JAVA ASM: all-Adapter processing flow table
-- Root: public boolean doApplication() only
-- Source data: JAVA_ASM_CLASS_DEF / JAVA_ASM_METHOD_DEF / JAVA_ASM_METHOD_CALL
-- Java writer: single-thread + single-row executeUpdate(); no JDBC batch
-- ============================================================

CREATE TABLE IF NOT EXISTS JAVA_ASM_PROCESSING_FLOW (
    ID                  BIGSERIAL PRIMARY KEY,
    GROUP_NAME          TEXT        NOT NULL,
    ADAPTER_JAR         TEXT        NOT NULL,
    ADAPTER_CLASS       TEXT        NOT NULL,
    ROOT_METHOD         TEXT        NOT NULL,

    -- Pre-order traversal sequence within one Adapter/root.
    -- ROOT row is always 0, child nodes are 1..N.
    FLOW_ORDER          BIGINT      NOT NULL,

    -- ROOT=0, direct calls from doApplication()=1, next level=2 ...
    DEPTH               INTEGER     NOT NULL,

    -- Human-readable hierarchy path. ROOT row='ROOT', children='1','1.1','1.2'...
    -- Use FLOW_ORDER, not lexical FLOW_PATH sort, when reproducing execution-display order.
    FLOW_PATH           TEXT        NOT NULL,
    SIBLING_NO          INTEGER     NOT NULL,

    -- Current displayed node. For an unresolved target, NODE_JAR is ''.
    NODE_JAR            TEXT        NOT NULL DEFAULT '',
    NODE_CLASS          TEXT        NOT NULL,
    NODE_METHOD         TEXT        NOT NULL,

    -- Parent/caller node. ROOT row uses empty strings.
    PARENT_JAR          TEXT        NOT NULL DEFAULT '',
    PARENT_CLASS        TEXT        NOT NULL DEFAULT '',
    PARENT_METHOD       TEXT        NOT NULL DEFAULT '',

    -- Call-site metadata. NULL for the ROOT row.
    ORIGIN_LINE         INTEGER,
    OPCODE              TEXT        NOT NULL DEFAULT '',
    DISPATCH            TEXT        NOT NULL DEFAULT '',
    RESOLUTION_STATUS   TEXT        NOT NULL DEFAULT '',
    RAW_METHOD_CALL_ID  BIGINT,

    -- Same semantics as processing_flow.txt markers.
    IS_CYCLE            BOOLEAN     NOT NULL DEFAULT FALSE,
    IS_ALREADY_EXPANDED BOOLEAN     NOT NULL DEFAULT FALSE,
    CANDIDATES          TEXT        NOT NULL DEFAULT ''
);

-- Main JavaScript/API access pattern: one Adapter flow in display order.
CREATE INDEX IF NOT EXISTS IDX_JAVA_ASM_PROCESSING_FLOW_ADAPTER
    ON JAVA_ASM_PROCESSING_FLOW (GROUP_NAME, ADAPTER_CLASS, FLOW_ORDER);

-- Reverse lookup: find all flows that contain a class.
CREATE INDEX IF NOT EXISTS IDX_JAVA_ASM_PROCESSING_FLOW_NODE
    ON JAVA_ASM_PROCESSING_FLOW (GROUP_NAME, NODE_CLASS);

-- Trace a generated flow node back to the raw ASM call row.
CREATE INDEX IF NOT EXISTS IDX_JAVA_ASM_PROCESSING_FLOW_RAW_CALL
    ON JAVA_ASM_PROCESSING_FLOW (RAW_METHOD_CALL_ID)
    WHERE RAW_METHOD_CALL_ID IS NOT NULL;

-- -----------------------------------------------------------------
-- Strongly recommended source-table indexes for all-Adapter rebuilding.
-- Skip any statement whose equivalent index already exists.
-- -----------------------------------------------------------------
CREATE INDEX IF NOT EXISTS IDX_JAVA_ASM_METHOD_CALL_FLOW_LOOKUP
    ON JAVA_ASM_METHOD_CALL
       (GROUP_NAME, ORIGIN_JAR, ORIGIN_CLASS, ID);

CREATE INDEX IF NOT EXISTS IDX_JAVA_ASM_METHOD_DEF_FLOW_ROOT
    ON JAVA_ASM_METHOD_DEF (GROUP_NAME, JAR_PATH, CLASS_NAME)
    WHERE METHOD_NAME = 'doApplication'
      AND DESCRIPTOR = '()Z'
      AND METHOD_ACCESS = 'public';

CREATE INDEX IF NOT EXISTS IDX_JAVA_ASM_CLASS_DEF_ADAPTER
    ON JAVA_ASM_CLASS_DEF
       (IS_ADAPTER, GROUP_NAME, JAR_PATH, CLASS_NAME);

-- ============================================================
-- Example: reproduce one Adapter flow for JavaScript/API use
-- ============================================================
-- SELECT
--     FLOW_ORDER,
--     DEPTH,
--     FLOW_PATH,
--     SIBLING_NO,
--     NODE_CLASS,
--     NODE_METHOD,
--     PARENT_CLASS,
--     PARENT_METHOD,
--     ORIGIN_LINE,
--     OPCODE,
--     DISPATCH,
--     RESOLUTION_STATUS,
--     IS_CYCLE,
--     IS_ALREADY_EXPANDED
-- FROM JAVA_ASM_PROCESSING_FLOW
-- WHERE GROUP_NAME = 'nikkoEZ/ez.web.online'
--   AND ADAPTER_CLASS = 'jp.co.eztrade.app.tsn_meigara.unyokaisya_kanri.adapter.TsnmeigUnyCorpDelexeAdapter'
-- ORDER BY FLOW_ORDER;
