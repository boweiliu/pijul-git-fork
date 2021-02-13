use super::change_id::*;
use super::vertex::*;

bitflags! {
    /// Possible flags of edges.
    #[derive(Serialize, Deserialize)]
    pub struct EdgeFlags: u8 {
        const BLOCK = 1;
        /// A pseudo-edge, computed when applying the change to
        /// restore connectivity, and/or mark conflicts.
        const PSEUDO = 4;
        /// An edge encoding file system hierarchy.
        const FOLDER = 16;
        /// A "reverse" edge (all edges in the graph have a reverse edge).
        const PARENT = 32;
        /// An edge whose target (if not also `PARENT`) or
        /// source (if also `PARENT`) is marked as deleted.
        const DELETED = 128;
    }
}

impl EdgeFlags {
    #[inline]
    pub(crate) fn db() -> Self {
        Self::DELETED | Self::BLOCK
    }

    #[inline]
    pub(crate) fn bp() -> Self {
        Self::BLOCK | Self::PARENT
    }

    #[inline]
    pub(crate) fn pseudof() -> Self {
        Self::PSEUDO | Self::FOLDER
    }

    #[inline]
    pub(crate) fn alive_children() -> Self {
        Self::BLOCK | Self::PSEUDO | Self::FOLDER
    }

    #[inline]
    pub(crate) fn parent_folder() -> Self {
        Self::PARENT | Self::FOLDER
    }

    #[inline]
    pub(crate) fn is_deleted(&self) -> bool {
        self.contains(EdgeFlags::DELETED)
    }
    #[inline]
    pub(crate) fn is_parent(&self) -> bool {
        self.contains(EdgeFlags::PARENT)
    }
    #[inline]
    pub(crate) fn is_folder(&self) -> bool {
        self.contains(EdgeFlags::FOLDER)
    }
    #[inline]
    pub(crate) fn is_block(&self) -> bool {
        self.contains(EdgeFlags::BLOCK)
    }
}

/// The target half of an edge in the repository graph.
#[derive(Clone, Copy, Debug, PartialEq, PartialOrd, Eq, Ord, Hash)]
#[doc(hidden)]
pub struct Edge {
    /// Flags of this edge.
    pub flag: EdgeFlags,
    /// Target of this edge.
    pub dest: Position<ChangeId>,
    /// Change that introduced this edge (possibly as a
    /// pseudo-edge, i.e. not explicitly in the change, but
    /// computed from it).
    pub introduced_by: ChangeId,
}
